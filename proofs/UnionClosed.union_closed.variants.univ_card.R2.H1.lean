import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R2

/-! Verification of the twelve-element union-closed minimum-three reduction step. -/

namespace UCH1Sol
open Finset UnionClosed


@[simp] lemma nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] lemma nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
@[simp] lemma nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] lemma nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
@[simp] lemma nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl
@[simp] lemma nat_pow_eq (a b : ℕ) : Nat.pow a b = a ^ b := rfl
@[simp] lemma nat_lor_eq (a b : ℕ) : Nat.lor a b = a ||| b := rfl
@[simp] lemma nat_ble_true (a b : ℕ) : (Nat.ble a b = true) = (a ≤ b) := Nat.ble_eq
@[simp] lemma nat_ble_false (a b : ℕ) : (Nat.ble a b = false) ↔ b < a := by
  rw [← Bool.not_eq_true, Nat.ble_eq]; omega
@[simp] lemma nat_blt_true (a b : ℕ) : (Nat.blt a b = true) = (a < b) := Nat.blt_eq
@[simp] lemma nat_blt_false (a b : ℕ) : (Nat.blt a b = false) ↔ b ≤ a := by
  rw [← Bool.not_eq_true, Nat.blt_eq]; omega
@[simp] lemma nat_beq_true (a b : ℕ) : (Nat.beq a b = true) = (a = b) := Nat.beq_eq
@[simp] lemma nat_beq_false (a b : ℕ) : (Nat.beq a b = false) ↔ a ≠ b := by
  rw [← Bool.not_eq_true, Nat.beq_eq]

def W16 : Nat := 0x10000
def W32 : Nat := 0x100000000
def W64 : Nat := 0x10000000000000000
def BIAS16 : Nat := 0x100000000

def decode (b m : ℕ) : Finset (Fin b) :=
  univ.filter (fun j : Fin b => m.testBit j.val)

def maskCard (b m : ℕ) : ℕ :=
  ((List.finRange b).filter (fun j : Fin b => m.testBit j.val)).length

lemma maskCard_eq_card (b m : ℕ) : maskCard b m = (decode b m).card := by
  unfold maskCard decode
  rw [card_def, Finset.filter_val]
  have h1 : (univ : Finset (Fin b)).val = ↑(List.finRange b) := by ext x; simp
  rw [h1, Multiset.filter_coe]
  simp

def HasPattern (b : ℕ) (P : List ℕ) (F : Finset (Finset (Fin 12))) : Prop :=
  ∃ e : Fin b ↪ Fin 12, ∀ m ∈ P, (decode b m).map e ∈ F

def hasBit (m i : Nat) : Bool :=
  Nat.beq (Nat.lor m (Nat.pow 2 i)) m

def setBit (m i : Nat) : Nat :=
  Nat.lor m (Nat.pow 2 i)

def swapBit (i j m : Nat) : Nat :=
  match hasBit m i with
  | true =>
    match hasBit m j with
    | true => m
    | false => Nat.xor m (Nat.xor (Nat.pow 2 i) (Nat.pow 2 j))
  | false =>
    match hasBit m j with
    | false => m
    | true => Nat.xor m (Nat.xor (Nat.pow 2 i) (Nat.pow 2 j))

lemma hasBit_eq_testBit (m i : ℕ) : hasBit m i = m.testBit i := by
  apply Bool.eq_iff_iff.mpr
  change Nat.beq (m ||| 2 ^ i) m = true ↔ m.testBit i = true
  rw [Nat.beq_eq]
  cases h : m.testBit i
  · simp only [Bool.false_eq_true, iff_false]
    intro heq
    have ht := congrArg (fun x => x.testBit i) heq
    rw [Nat.testBit_lor, Nat.testBit_two_pow] at ht
    simp [h] at ht
  · simp only [iff_true]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_lor, Nat.testBit_two_pow]
    by_cases hik : i = k
    · subst hik; simp [h]
    · simp [hik]

lemma setBit_testBit (m i k : ℕ) : (setBit m i).testBit k = (m.testBit k || decide (i = k)) := by
  change (m ||| 2 ^ i).testBit k = _
  rw [Nat.testBit_lor, Nat.testBit_two_pow]

lemma swapBit_testBit (i j m k : ℕ) :
    (swapBit i j m).testBit k = m.testBit (if k = i then j else if k = j then i else k) := by
  unfold swapBit
  rw [hasBit_eq_testBit, hasBit_eq_testBit]
  have hxor (x : ℕ) : (Nat.xor x (Nat.xor (Nat.pow 2 i) (Nat.pow 2 j))).testBit k =
      bne (x.testBit k) (bne (decide (i = k)) (decide (j = k))) := by
    change (x ^^^ ((2 ^ i) ^^^ (2 ^ j))).testBit k = _
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
  cases hmi : m.testBit i <;> cases hmj : m.testBit j
  · dsimp only
    by_cases hki : k = i
    · subst hki; rw [if_pos rfl, hmi, hmj]
    · rw [if_neg hki]
      by_cases hkj : k = j
      · subst hkj; rw [if_pos rfl, hmj, hmi]
      · rw [if_neg hkj]
  · dsimp only; rw [hxor]
    have hij : i ≠ j := by rintro rfl; rw [hmi] at hmj; cases hmj
    by_cases hki : k = i
    · subst hki; simp [hij.symm, hmi, hmj]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hij, hmi, hmj]
      · have h1 : i ≠ k := fun h => hki h.symm
        have h2 : j ≠ k := fun h => hkj h.symm
        simp [hki, hkj, h1, h2]
  · dsimp only; rw [hxor]
    have hij : i ≠ j := by rintro rfl; rw [hmi] at hmj; cases hmj
    by_cases hki : k = i
    · subst hki; simp [hij.symm, hmi, hmj]
    · by_cases hkj : k = j
      · subst hkj; simp [hki, hij, hmi, hmj]
      · have h1 : i ≠ k := fun h => hki h.symm
        have h2 : j ≠ k := fun h => hkj h.symm
        simp [hki, hkj, h1, h2]
  · dsimp only
    by_cases hki : k = i
    · subst hki; rw [if_pos rfl, hmi, hmj]
    · rw [if_neg hki]
      by_cases hkj : k = j
      · subst hkj; rw [if_pos rfl, hmj, hmi]
      · rw [if_neg hkj]

lemma decode_swapBit {b i j : ℕ} (hi : i < b) (hj : j < b) (m : ℕ) :
    decode b (swapBit i j m) = (decode b m).map (Equiv.swap (⟨i, hi⟩ : Fin b) ⟨j, hj⟩).toEmbedding := by
  ext x
  simp only [decode, mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
  rw [swapBit_testBit]
  let a : Fin b := ⟨i, hi⟩
  let c : Fin b := ⟨j, hj⟩
  constructor
  · intro hx
    refine ⟨Equiv.swap a c x, ?_, Equiv.swap_apply_self a c x⟩
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · have hxv : x.val = i := congrArg Fin.val h1
      simpa [c, hxv] using hx
    · have hxv : x.val = j := congrArg Fin.val h2
      have hne : j ≠ i := fun h => h1 (Fin.ext (hxv.trans h))
      simpa [a, hxv, hne] using hx
    · have h1' : x.val ≠ i := fun h => h1 (Fin.ext h)
      have h2' : x.val ≠ j := fun h => h2 (Fin.ext h)
      simpa [h1', h2'] using hx
  · rintro ⟨y, hy, rfl⟩
    set z : Fin b := Equiv.swap a c y
    have hyx : Equiv.swap a c z = y := Equiv.swap_apply_self a c y
    rw [← hyx, Equiv.swap_apply_def] at hy
    split_ifs at hy with h1 h2
    · have hzv : z.val = i := congrArg Fin.val h1
      simpa [c, hzv] using hy
    · have hzv : z.val = j := congrArg Fin.val h2
      have hne : j ≠ i := fun h => h1 (Fin.ext (hzv.trans h))
      simpa [a, hzv, hne] using hy
    · have h1' : z.val ≠ i := fun h => h1 (Fin.ext h)
      have h2' : z.val ≠ j := fun h => h2 (Fin.ext h)
      simpa [h1', h2'] using hy

def listGet? : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ i => listGet? xs i

lemma listGet?_mem : ∀ (xs : List α) (i : ℕ) (v : α), listGet? xs i = some v → v ∈ xs
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by simp [listGet?] at h; subst h; exact List.mem_cons_self
  | _ :: xs, i + 1, v, h => List.mem_cons_of_mem _ (listGet?_mem xs i v h)

lemma listGet?_eq_getElem? : ∀ (xs : List α) (i : ℕ), listGet? xs i = xs[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, i + 1 => listGet?_eq_getElem? xs i

def listGetD : List Nat → Nat → Nat → Nat
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, Nat.succ i, d => listGetD xs i d

lemma listGetD_eq_getD : ∀ (xs : List ℕ) (i d : ℕ), listGetD xs i d = xs.getD i d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, d => listGetD_eq_getD xs i d

def listContainsNat : List Nat → Nat → Bool
  | [], _ => false
  | x :: xs, y => match Nat.beq x y with | true => true | false => listContainsNat xs y

lemma listContainsNat_iff : ∀ (xs : List ℕ) (y : ℕ), listContainsNat xs y = true ↔ y ∈ xs
  | [], _ => by simp [listContainsNat]
  | x :: xs, y => by
    dsimp [listContainsNat]
    cases h : Nat.beq x y
    · rw [listContainsNat_iff xs y]
      have hne : x ≠ y := fun heq => by rw [Nat.beq_eq.mpr heq] at h; cases h
      simp [hne.symm]
    · have heq := Nat.beq_eq.mp h; subst heq; simp

def listAll (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => match p x with | true => listAll p xs | false => false

lemma listAll_iff (p : α → Bool) : ∀ (xs : List α), listAll p xs = true ↔ ∀ x ∈ xs, p x = true
  | [] => by simp [listAll]
  | x :: xs => by
    dsimp [listAll]
    cases hp : p x
    · simp [hp]
    · rw [listAll_iff p xs]; simp [hp]

def listAny (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => match p x with | true => true | false => listAny p xs

lemma listAny_iff (p : α → Bool) : ∀ (xs : List α), listAny p xs = true ↔ ∃ x ∈ xs, p x = true
  | [] => by simp [listAny]
  | x :: xs => by
    dsimp [listAny]
    cases hp : p x
    · rw [listAny_iff p xs]; simp [hp]
    · simp [hp]

def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => match listContainsNat xs x with | true => false | false => nodupNat xs

lemma nodupNat_sound : ∀ (xs : List ℕ), nodupNat xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    dsimp [nodupNat] at h
    cases hc : listContainsNat xs x
    · rw [hc] at h
      have hnot : x ∉ xs := fun hm => by rw [(listContainsNat_iff xs x).mpr hm] at hc; cases hc
      exact List.nodup_cons.mpr ⟨hnot, nodupNat_sound xs h⟩
    · rw [hc] at h; cases h

def listToMask : List Nat → Nat
  | [] => 0
  | u :: us => setBit (listToMask us) u

lemma listToMask_testBit : ∀ (l : List ℕ) (i : ℕ), (listToMask l).testBit i = true ↔ i ∈ l
  | [], i => by simp [listToMask]
  | u :: us, i => by
    simp only [listToMask, setBit_testBit, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    rw [listToMask_testBit us i]; tauto

def popCountAux : Nat → Nat → Nat
  | 0, _ => 0
  | Nat.succ k, m => Nat.add (Nat.mod m 2) (popCountAux k (Nat.div m 2))

lemma popCountAux_eq_maskCard_check :
    ((List.range 8).all (fun b =>
      (List.range (2 ^ b)).all (fun u => popCountAux b u == maskCard b u))) = true := by
  decide +kernel

lemma popCountAux_eq_card {b u : ℕ} (hb : b ≤ 7) (hu : u < 2 ^ b) :
    popCountAux b u = (decode b u).card := by
  have h := popCountAux_eq_maskCard_check
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h b (by omega) u hu, maskCard_eq_card]

def maskWeightRec : List Nat → Nat → Nat
  | [], _ => 0
  | w :: ws, x =>
    let wj := match Nat.beq (Nat.mod x 2) 1 with | true => w | false => 0
    Nat.add wj (maskWeightRec ws (Nat.div x 2))

lemma maskWeightRec_eq_sum : ∀ (w_in : List ℕ) (b u : ℕ), w_in.length = b →
    (maskWeightRec w_in u : ℤ) = ∑ j ∈ decode b u, (w_in.getD j.val 0 : ℤ)
  | [], b, u, hlen => by
    subst hlen
    have hem : decode 0 u = ∅ := by ext x; exact Fin.elim0 x
    simp [maskWeightRec, hem]
  | w :: ws, b + 1, u, hlen => by
    have hlen' : ws.length = b := by simpa using hlen
    simp only [maskWeightRec, nat_add_eq, nat_div_eq, nat_mod_eq]
    have ih := maskWeightRec_eq_sum ws b (u / 2) hlen'
    have hsplit : (∑ j ∈ decode (b + 1) u, ((w :: ws).getD j.val 0 : ℤ)) =
        (if u.testBit 0 then (w : ℤ) else 0) + ∑ k ∈ decode b (u / 2), (ws.getD k.val 0 : ℤ) := by
      simp only [decode, sum_filter]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero, List.getD_cons_succ]
      congr 1
      apply sum_congr rfl; intro k _
      have htb : (u / 2).testBit k.val = u.testBit (k.val + 1) := by
        rw [← Nat.shiftRight_eq_div_pow (m := u) (n := 1), Nat.testBit_shiftRight, Nat.add_comm]
      rw [htb]
    rw [hsplit, ← ih]
    have htb0 : u.testBit 0 = Nat.beq (u % 2) 1 := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.testBit_zero, decide_eq_true_eq, Nat.beq_eq]
    rw [htb0]
    cases Nat.beq (u % 2) 1 <;> simp

def lexVal (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 2 ^ xs.length else 0) + lexVal p xs

lemma lexVal_lt_two_pow (p : ℕ → Bool) : ∀ (l : List ℕ), lexVal p l < 2 ^ l.length
  | [] => by simp [lexVal]
  | x :: xs => by
    dsimp [lexVal]
    have ih := lexVal_lt_two_pow p xs
    have hpow : 2 ^ (xs.length + 1) = 2 ^ xs.length + 2 ^ xs.length := by rw [Nat.pow_succ]; omega
    split_ifs <;> omega

def symStepPrefix (zm om i j u : Nat) : List Nat → Bool
  | [] => false
  | x :: xs =>
    match Nat.beq x u with
    | true => true
    | false =>
      let y := swapBit i j x
      let eqXY := match Nat.beq x y with
        | true => true
        | false => (hasBit zm x && hasBit zm y) || (hasBit om x && hasBit om y)
      match eqXY with
      | false => false
      | true => symStepPrefix zm om i j u xs

lemma symStepPrefix_lt {p : ℕ → Bool} {zm om i j u : ℕ}
    (hz : ∀ x, zm.testBit x = true → p x = false)
    (ho : ∀ x, om.testBit x = true → p x = true)
    (hpu : p u = false) (hpus : p (swapBit i j u) = true) :
    ∀ (ord : List ℕ), symStepPrefix zm om i j u ord = true →
      lexVal p ord < lexVal (fun x => p (swapBit i j x)) ord
  | [], h => by cases h
  | x :: xs, h => by
    dsimp [symStepPrefix] at h
    cases hxu : Nat.beq x u
    · rw [hxu] at h; dsimp only at h
      have hx_eq : p x = p (swapBit i j x) := by
        cases hxy : Nat.beq x (swapBit i j x)
        · rw [hxy] at h
          cases hor : ((hasBit zm x && hasBit zm (swapBit i j x)) || (hasBit om x && hasBit om (swapBit i j x)))
          · rw [hor] at h; cases h
          · simp only [Bool.or_eq_true, Bool.and_eq_true, hasBit_eq_testBit] at hor
            rcases hor with ⟨hz1, hz2⟩ | ⟨ho1, ho2⟩
            · rw [hz _ hz1, hz _ hz2]
            · rw [ho _ ho1, ho _ ho2]
        · exact congrArg p (Nat.beq_eq.mp hxy)
      have hrest : symStepPrefix zm om i j u xs = true := by
        revert h; cases Nat.beq x (swapBit i j x) <;>
          cases ((hasBit zm x && hasBit zm (swapBit i j x)) || (hasBit om x && hasBit om (swapBit i j x))) <;> simp
      have ih := symStepPrefix_lt hz ho hpu hpus xs hrest
      dsimp [lexVal]
      cases hpx : p x
      · have hps : p (swapBit i j x) = false := hx_eq.symm.trans hpx
        simp [hps, ih]
      · have hps : p (swapBit i j x) = true := hx_eq.symm.trans hpx
        simp [hps, ih]
    · have heq := Nat.beq_eq.mp hxu; subst heq
      dsimp [lexVal]
      simp only [hpu, hpus, Bool.false_eq_true, ↓reduceIte, zero_add]
      have hlt := lexVal_lt_two_pow p xs
      omega

def checkSwaps (b : Nat) (w_in P_cl : List Nat) (pMaskBig : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | p :: rest =>
    let i := p.1
    let j := p.2
    match (Nat.blt i b && Nat.blt j b &&
           Nat.beq (listGetD w_in i 0) (listGetD w_in j 0) &&
           listAll (fun m => hasBit pMaskBig (swapBit i j m)) P_cl) with
    | false => false
    | true => checkSwaps b w_in P_cl pMaskBig rest

lemma checkSwaps_mem {b : ℕ} {w_in P_cl : List ℕ} :
    ∀ (swaps : List (ℕ × ℕ)),
      checkSwaps b w_in P_cl (listToMask P_cl) swaps = true →
      ∀ p ∈ swaps, p.1 < b ∧ p.2 < b ∧ w_in.getD p.1 0 = w_in.getD p.2 0 ∧
        (∀ m ∈ P_cl, swapBit p.1 p.2 m ∈ P_cl)
  | [], _, _, hp => by cases hp
  | q :: rest, hok, p, hp => by
    dsimp [checkSwaps] at hok
    cases hc : (Nat.blt q.1 b && Nat.blt q.2 b &&
           Nat.beq (listGetD w_in q.1 0) (listGetD w_in q.2 0) &&
           listAll (fun m => hasBit (listToMask P_cl) (swapBit q.1 q.2 m)) P_cl)
    · rw [hc] at hok; cases hok
    · rw [hc] at hok
      rcases List.mem_cons.mp hp with rfl | hmem
      · simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, listGetD_eq_getD,
          listAll_iff, hasBit_eq_testBit, listToMask_testBit] at hc
        exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
      · exact checkSwaps_mem rest hok p hmem

lemma exists_sym_canonical_emb {b : ℕ} (F : Finset (Finset (Fin 12))) (K : Finset (Fin 12))
    (e0 : Fin b ↪ Fin 12) (w_in P_cl : List ℕ) (swaps : List (ℕ × ℕ)) (ord : List ℕ)
    (hP0 : ∀ m ∈ P_cl, (decode b m).map e0 ∈ F)
    (hsw : checkSwaps b w_in P_cl (listToMask P_cl) swaps = true) :
    let wF (j : Fin b) : ℕ := w_in.getD j.val 0
    ∃ e : Fin b ↪ Fin 12,
      univ.map e = univ.map e0 ∧
      (∀ x : Fin 12, (∑ j : Fin b, if e j = x then wF j else 0) = (∑ j : Fin b, if e0 j = x then wF j else 0)) ∧
      (∀ m ∈ P_cl, (decode b m).map e ∈ F) ∧
      (∀ p ∈ swaps,
        lexVal (fun u => decide (K ∪ (decode b (swapBit p.1 p.2 u)).map e ∈ F)) ord ≤
          lexVal (fun u => decide (K ∪ (decode b u).map e ∈ F)) ord) := by
  classical
  intro wF
  let Valid (σ : Equiv.Perm (Fin b)) : Prop :=
    (∀ x : Fin b, wF (σ x) = wF x) ∧
    (∀ m ∈ P_cl, (decode b m).map (σ.toEmbedding.trans e0) ∈ F)
  let S : Finset (Equiv.Perm (Fin b)) := univ.filter Valid
  have h1S : (1 : Equiv.Perm (Fin b)) ∈ S := by
    simp only [S, mem_filter, mem_univ, true_and, Valid]
    refine ⟨fun _ => rfl, ?_⟩
    intro m hm
    have heq : (1 : Equiv.Perm (Fin b)).toEmbedding.trans e0 = e0 := by ext; rfl
    rw [heq]; exact hP0 m hm
  let score (σ : Equiv.Perm (Fin b)) : ℕ :=
    lexVal (fun u => decide (K ∪ (decode b u).map (σ.toEmbedding.trans e0) ∈ F)) ord
  obtain ⟨σ, hσS, hmax⟩ := exists_max_image S score ⟨1, h1S⟩
  obtain ⟨hσw, hσP⟩ := (mem_filter.mp hσS).2
  let e : Fin b ↪ Fin 12 := σ.toEmbedding.trans e0
  refine ⟨e, ?_, ?_, hσP, ?_⟩
  · ext y
    simp only [e, mem_map, mem_univ, true_and, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨σ j, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨σ.symm k, by simp⟩
  · intro x
    have hrew : (∑ j : Fin b, if e j = x then wF j else 0) =
        ∑ j : Fin b, if e0 (σ j) = x then wF (σ j) else 0 := by
      apply sum_congr rfl; intro j _
      change (if e0 (σ j) = x then wF j else 0) = _
      rw [hσw j]
    rw [hrew]
    exact Equiv.sum_comp σ (fun k => if e0 k = x then wF k else 0)
  · intro p hp
    obtain ⟨hi, hj, hwij, hPswap⟩ := checkSwaps_mem swaps hsw p hp
    let τ : Equiv.Perm (Fin b) := Equiv.swap ⟨p.1, hi⟩ ⟨p.2, hj⟩
    let σ' : Equiv.Perm (Fin b) := τ.trans σ
    have hemb : σ'.toEmbedding.trans e0 = τ.toEmbedding.trans e := by ext; rfl
    have hτw : ∀ y : Fin b, wF (τ y) = wF y := by
      intro y
      dsimp [τ]; rw [Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hwij.symm
      · subst h2; exact hwij
      · rfl
    have hσ'S : σ' ∈ S := by
      simp only [S, mem_filter, mem_univ, true_and, Valid]
      refine ⟨fun y => (hσw (τ y)).trans (hτw y), ?_⟩
      intro m hm
      rw [hemb, ← map_map, ← decode_swapBit hi hj m]
      exact hσP _ (hPswap m hm)
    have hle := hmax σ' hσ'S
    have hsc_eq : score σ' = lexVal (fun u => decide (K ∪ (decode b (swapBit p.1 p.2 u)).map e ∈ F)) ord := by
      dsimp [score]
      congr 1; funext u
      rw [hemb, ← map_map, ← decode_swapBit hi hj u]
    rwa [← hsc_eq]

inductive Arr8 (α : Type) where
  | empty
  | leaf (v : α)
  | node (s : Nat) (c0 c1 c2 c3 c4 c5 c6 c7 : Arr8 α)

def buildArr8Aux (xs : List α) : Nat → Arr8 α × List α
  | 0 => match xs with
    | [] => (Arr8.empty, [])
    | x :: rest => (Arr8.leaf x, rest)
  | Nat.succ d =>
    match buildArr8Aux xs d with
    | (c0, x1) => match buildArr8Aux x1 d with
    | (c1, x2) => match buildArr8Aux x2 d with
    | (c2, x3) => match buildArr8Aux x3 d with
    | (c3, x4) => match buildArr8Aux x4 d with
    | (c4, x5) => match buildArr8Aux x5 d with
    | (c5, x6) => match buildArr8Aux x6 d with
    | (c6, x7) => match buildArr8Aux x7 d with
    | (c7, x8) => (Arr8.node (Nat.pow 8 d) c0 c1 c2 c3 c4 c5 c6 c7, x8)

def log8Ceil : Nat → Nat → Nat → Nat
  | 0, _, d => d
  | Nat.succ fuel, n, d =>
    match Nat.ble n (Nat.pow 8 d) with
    | true => d
    | false => log8Ceil fuel n (Nat.add d 1)

def listToArr8 (xs : List α) : Arr8 α :=
  (buildArr8Aux xs (log8Ceil 5 xs.length 0)).1

def getArr8? (a : Arr8 α) (idx : Nat) : Option α :=
  match a with
  | Arr8.empty => none
  | Arr8.leaf v => match Nat.beq idx 0 with | true => some v | false => none
  | Arr8.node s c0 c1 c2 c3 c4 c5 c6 c7 =>
    let q := Nat.div idx s
    let r := Nat.mod idx s
    match Nat.blt q 4 with
    | true =>
      match Nat.blt q 2 with
      | true => match Nat.beq q 0 with | true => getArr8? c0 r | false => getArr8? c1 r
      | false => match Nat.beq q 2 with | true => getArr8? c2 r | false => getArr8? c3 r
    | false =>
      match Nat.blt q 6 with
      | true => match Nat.beq q 4 with | true => getArr8? c4 r | false => getArr8? c5 r
      | false => match Nat.beq q 6 with | true => getArr8? c6 r | false => getArr8? c7 r

def AllArr8 (P : α → Prop) : Arr8 α → Prop
  | Arr8.empty => True
  | Arr8.leaf v => P v
  | Arr8.node _ c0 c1 c2 c3 c4 c5 c6 c7 =>
    AllArr8 P c0 ∧ AllArr8 P c1 ∧ AllArr8 P c2 ∧ AllArr8 P c3 ∧
    AllArr8 P c4 ∧ AllArr8 P c5 ∧ AllArr8 P c6 ∧ AllArr8 P c7

lemma buildArr8Aux_all (P : α → Prop) :
    ∀ (d : ℕ) (xs : List α), (∀ x ∈ xs, P x) →
      AllArr8 P (buildArr8Aux xs d).1 ∧ (∀ x ∈ (buildArr8Aux xs d).2, P x)
  | 0, [], _ => ⟨trivial, fun _ h => by cases h⟩
  | 0, x :: rest, hxs => ⟨hxs x List.mem_cons_self, fun y hy => hxs y (List.mem_cons_of_mem _ hy)⟩
  | d + 1, xs, hxs => by
    dsimp [buildArr8Aux]
    obtain ⟨h0, r1⟩ := buildArr8Aux_all P d xs hxs
    obtain ⟨h1, r2⟩ := buildArr8Aux_all P d _ r1
    obtain ⟨h2, r3⟩ := buildArr8Aux_all P d _ r2
    obtain ⟨h3, r4⟩ := buildArr8Aux_all P d _ r3
    obtain ⟨h4, r5⟩ := buildArr8Aux_all P d _ r4
    obtain ⟨h5, r6⟩ := buildArr8Aux_all P d _ r5
    obtain ⟨h6, r7⟩ := buildArr8Aux_all P d _ r6
    obtain ⟨h7, r8⟩ := buildArr8Aux_all P d _ r7
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, r8⟩

lemma getArr8?_prop (P : α → Prop) :
    ∀ (a : Arr8 α) (idx : ℕ) (v : α), AllArr8 P a → getArr8? a idx = some v → P v
  | Arr8.empty, _, _, _, h => by cases h
  | Arr8.leaf w, idx, v, hw, h => by
    dsimp [getArr8?] at h
    cases hb : Nat.beq idx 0
    · rw [hb] at h; cases h
    · rw [hb] at h; simp at h; subst h; exact hw
  | Arr8.node s c0 c1 c2 c3 c4 c5 c6 c7, idx, v, ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩, h => by
    dsimp [getArr8?] at h
    set q := idx / s
    set r := idx % s
    cases hb4 : Nat.blt q 4
    · rw [hb4] at h
      cases hb6 : Nat.blt q 6
      · rw [hb6] at h
        cases hq6 : Nat.beq q 6
        · rw [hq6] at h; exact getArr8?_prop P c7 r v h7 h
        · rw [hq6] at h; exact getArr8?_prop P c6 r v h6 h
      · rw [hb6] at h
        cases hq4 : Nat.beq q 4
        · rw [hq4] at h; exact getArr8?_prop P c5 r v h5 h
        · rw [hq4] at h; exact getArr8?_prop P c4 r v h4 h
    · rw [hb4] at h
      cases hb2 : Nat.blt q 2
      · rw [hb2] at h
        cases hq2 : Nat.beq q 2
        · rw [hq2] at h; exact getArr8?_prop P c3 r v h3 h
        · rw [hq2] at h; exact getArr8?_prop P c2 r v h2 h
      · rw [hb2] at h
        cases hq0 : Nat.beq q 0
        · rw [hq0] at h; exact getArr8?_prop P c1 r v h1 h
        · rw [hq0] at h; exact getArr8?_prop P c0 r v h0 h

lemma getArr8?_mem (xs : List α) (idx : ℕ) (v : α)
    (h : getArr8? (listToArr8 xs) idx = some v) : v ∈ xs :=
  getArr8?_prop (· ∈ xs) _ idx v (buildArr8Aux_all (· ∈ xs) _ xs (fun _ hx => hx)).1 h

def mapMaskAux : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, m => (if m.testBit 0 then 1 <<< x else 0) ||| mapMaskAux xs (m >>> 1)

def sigValid : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | Nat.succ r, bk, sb, seen =>
    let x := Nat.mod sb 16
    match (Nat.blt x bk && !(hasBit seen x)) with
    | false => false
    | true => sigValid r bk (Nat.div sb 16) (setBit seen x)

def mapMaskPacked : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | Nat.succ r, sb, m =>
    let rest := mapMaskPacked r (Nat.div sb 16) (Nat.div m 2)
    match Nat.beq (Nat.mod m 2) 1 with
    | true => setBit rest (Nat.mod sb 16)
    | false => rest

def unpackSig : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, sb => (sb % 16) :: unpackSig r (sb / 16)

lemma unpackSig_length : ∀ (r sb : ℕ), (unpackSig r sb).length = r
  | 0, _ => rfl
  | r + 1, sb => by simp [unpackSig, unpackSig_length r]

lemma sigValid_sound : ∀ (r bk sb seen : ℕ), sigValid r bk sb seen = true →
    (unpackSig r sb).Nodup ∧ (∀ y ∈ unpackSig r sb, y < bk ∧ seen.testBit y = false)
  | 0, _, _, _, _ => ⟨List.nodup_nil, fun _ h => by cases h⟩
  | r + 1, bk, sb, seen, h => by
    dsimp [sigValid, unpackSig] at h ⊢
    cases hc : (Nat.blt (sb % 16) bk && !(hasBit seen (sb % 16)))
    · rw [hc] at h; cases h
    · rw [hc] at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true', hasBit_eq_testBit] at hc
      obtain ⟨hnd, hall⟩ := sigValid_sound r bk (sb / 16) (setBit seen (sb % 16)) h
      have hnot : (sb % 16) ∉ unpackSig r (sb / 16) := by
        intro hm
        have hs := (hall _ hm).2
        rw [setBit_testBit] at hs
        simp at hs
      refine ⟨List.nodup_cons.mpr ⟨hnot, hnd⟩, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hmem
      · exact hc
      · obtain ⟨hlt, hs⟩ := hall y hmem
        rw [setBit_testBit, Bool.or_eq_false_iff] at hs
        exact ⟨hlt, hs.1⟩

lemma mapMaskPacked_eq : ∀ (r sb m : ℕ), mapMaskPacked r sb m = mapMaskAux (unpackSig r sb) m
  | 0, _, _ => rfl
  | r + 1, sb, m => by
    dsimp [mapMaskPacked, unpackSig, mapMaskAux]
    have hdivm : m / 2 = m >>> 1 := by rw [Nat.shiftRight_eq_div_pow, pow_one]
    rw [hdivm, mapMaskPacked_eq r (sb / 16) (m >>> 1)]
    have htb0 : m.testBit 0 = Nat.beq (m % 2) 1 := by
      apply Bool.eq_iff_iff.mpr
      rw [Nat.testBit_zero, decide_eq_true_eq, Nat.beq_eq]
    rw [htb0]
    cases Nat.beq (m % 2) 1
    · simp
    · simp only [↓reduceIte]
      change (mapMaskAux (unpackSig r (sb / 16)) (m >>> 1)) ||| (2 ^ (sb % 16)) =
        (1 <<< (sb % 16)) ||| mapMaskAux (unpackSig r (sb / 16)) (m >>> 1)
      rw [Nat.one_shiftLeft, Nat.lor_comm]

def checkPmLoop (bp sb top n2b pMaskBig : Nat) (cl : List Nat) : List Nat → Bool
  | [] => true
  | m' :: ms =>
    let M := mapMaskPacked bp sb m'
    match ((Nat.blt M n2b && hasBit pMaskBig M) || listAny (fun u => Nat.beq M (Nat.lor u top)) cl) with
    | false => false
    | true => checkPmLoop bp sb top n2b pMaskBig cl ms

lemma checkPmLoop_iff (bp sb top n2b pMaskBig : ℕ) (cl : List ℕ) :
    ∀ (pm : List ℕ), checkPmLoop bp sb top n2b pMaskBig cl pm = true ↔
      ∀ m' ∈ pm,
        let M := mapMaskPacked bp sb m'
        (M < n2b ∧ pMaskBig.testBit M = true) ∨ (∃ u ∈ cl, M = (u ||| top))
  | [] => by simp [checkPmLoop]
  | m' :: ms => by
    dsimp [checkPmLoop]
    set M := mapMaskPacked bp sb m'
    cases hc : ((Nat.blt M n2b && hasBit pMaskBig M) || listAny (fun u => Nat.beq M (Nat.lor u top)) cl)
    · constructor
      · intro h; cases h
      · intro hall
        have hm := hall m' List.mem_cons_self
        have hct : ((Nat.blt M n2b && hasBit pMaskBig M) || listAny (fun u => Nat.beq M (Nat.lor u top)) cl) = true := by
          simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, hasBit_eq_testBit,
            listAny_iff, Nat.beq_eq, nat_lor_eq]
          exact hm
        rw [hct] at hc; cases hc
    · rw [checkPmLoop_iff bp sb top n2b pMaskBig cl ms]
      have hm : (M < n2b ∧ pMaskBig.testBit M = true) ∨ (∃ u ∈ cl, M = (u ||| top)) := by
        simpa only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, hasBit_eq_testBit,
          listAny_iff, Nat.beq_eq, nat_lor_eq] using hc
      constructor
      · intro hms x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hm
        · exact hms x hmem
      · intro hall x hx
        exact hall x (List.mem_cons_of_mem _ hx)

def checkExclPacked (bp : Nat) (pm : List Nat) (top n2b bk pMaskBig sigBits : Nat) (cl : List Nat) : Bool :=
  sigValid bp bk sigBits 0 &&
  listAll (fun x => Nat.blt x n2b) cl &&
  checkPmLoop bp sigBits top n2b pMaskBig cl pm

def laneShift16 (i : Nat) : Nat :=
  Nat.pow 2 (Nat.mul 16 i)

def packVec16 : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, f, base => f base + W16 * packVec16 n f (base + 1)

lemma packVec16_congr : ∀ (n : ℕ) (f g : ℕ → ℕ) (base : ℕ),
    (∀ k < n, f (base + k) = g (base + k)) → packVec16 n f base = packVec16 n g base
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, base, h => by
    dsimp [packVec16]
    have h0 := h 0 (Nat.zero_lt_succ n)
    simp only [Nat.add_zero] at h0
    have ih := packVec16_congr n f g (base + 1) (fun k hk => by
      have := h (k + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    rw [h0, ih]

lemma packVec16_zero : ∀ (n base : ℕ), packVec16 n (fun _ => 0) base = 0
  | 0, _ => rfl
  | n + 1, base => by simp [packVec16, packVec16_zero n (base + 1)]

lemma packVec16_eq_zero_of (n : ℕ) (f : ℕ → ℕ) (base : ℕ)
    (h : ∀ k < n, f (base + k) = 0) : packVec16 n f base = 0 := by
  rw [packVec16_congr n f (fun _ => 0) base (fun k hk => h k hk), packVec16_zero]

lemma packVec16_eq_zero_iff : ∀ (n : ℕ) (f : ℕ → ℕ) (base : ℕ),
    packVec16 n f base = 0 → ∀ k < n, f (base + k) = 0
  | 0, _, _, _, _, hk => by omega
  | n + 1, f, base, hz, k, hk => by
    dsimp [packVec16] at hz
    have hW : 0 < W16 := by decide
    have hf0 : f base = 0 := by omega
    have hrest : packVec16 n f (base + 1) = 0 := by
      rcases Nat.eq_zero_or_pos (packVec16 n f (base + 1)) with h0 | hpos
      · exact h0
      · have : W16 * 1 ≤ W16 * packVec16 n f (base + 1) := Nat.mul_le_mul_left W16 hpos
        omega
    cases k with
    | zero => simpa using hf0
    | succ k' =>
      have := packVec16_eq_zero_iff n f (base + 1) hrest k' (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

lemma packVec16_add : ∀ (n : ℕ) (f g : ℕ → ℕ) (base : ℕ),
    packVec16 n f base + packVec16 n g base = packVec16 n (fun i => f i + g i) base
  | 0, _, _, _ => rfl
  | n + 1, f, g, base => by
    simp only [packVec16]
    have ih := packVec16_add n f g (base + 1)
    calc (f base + W16 * packVec16 n f (base + 1)) + (g base + W16 * packVec16 n g (base + 1))
        = (f base + g base) + W16 * (packVec16 n f (base + 1) + packVec16 n g (base + 1)) := by ring
      _ = (f base + g base) + W16 * packVec16 n (fun i => f i + g i) (base + 1) := by rw [ih]

lemma packVec16_mul (m : ℕ) : ∀ (n : ℕ) (f : ℕ → ℕ) (base : ℕ),
    m * packVec16 n f base = packVec16 n (fun i => m * f i) base
  | 0, _, _ => by simp [packVec16]
  | n + 1, f, base => by
    simp only [packVec16, mul_add, ← mul_assoc]
    have hcomm : m * W16 * packVec16 n f (base + 1) = W16 * (m * packVec16 n f (base + 1)) := by ring
    rw [hcomm, packVec16_mul m n f (base + 1)]

lemma laneShift16_eq_pow (i : ℕ) : laneShift16 i = W16 ^ i := by
  unfold laneShift16 W16
  have h16 : (0x10000 : ℕ) = 2 ^ 16 := by decide
  rw [h16, nat_pow_eq, nat_mul_eq, ← Nat.pow_mul]

lemma packVec16_single : ∀ (n base u : ℕ), base ≤ u → u < base + n →
    packVec16 n (fun i => if i = u then 1 else 0) base = W16 ^ (u - base)
  | 0, _, _, _, hlt => by omega
  | n + 1, base, u, hle, hlt => by
    dsimp [packVec16]
    by_cases heq : base = u
    · subst heq
      rw [if_pos rfl, packVec16_eq_zero_of n _ (base + 1) (by intro k _; simp; omega)]
      simp
    · rw [if_neg heq, zero_add, packVec16_single n (base + 1) u (by omega) (by omega)]
      have hsub : u - base = (u - (base + 1)) + 1 := by omega
      rw [hsub, Nat.pow_succ, mul_comm]

def sumLaneShifts16 : List Nat → Nat
  | [] => 0
  | u :: us => Nat.add (laneShift16 u) (sumLaneShifts16 us)

lemma sumLaneShifts16_eq (n : ℕ) : ∀ (cl : List ℕ), cl.Nodup → (∀ u ∈ cl, u < n) →
    sumLaneShifts16 cl = packVec16 n (fun i => if i ∈ cl then 1 else 0) 0
  | [], _, _ => by rw [packVec16_eq_zero_of n _ 0 (by simp)]; rfl
  | u :: us, hnd, hlt => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hu : u < n := hlt u List.mem_cons_self
    have hus : ∀ x ∈ us, x < n := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    change laneShift16 u + sumLaneShifts16 us = _
    rw [laneShift16_eq_pow, ← Nat.sub_zero u, ← packVec16_single n 0 u (Nat.zero_le u) (by omega),
        Nat.sub_zero, sumLaneShifts16_eq n us hnd' hus, packVec16_add]
    apply packVec16_congr; intro k _
    by_cases hku : k = u
    · subst hku; simp [hnot]
    · by_cases hkus : k ∈ us <;> simp [hku, hkus]

lemma packVec16_split : ∀ (m1 m2 : ℕ) (f : ℕ → ℕ) (base : ℕ),
    packVec16 (m1 + m2) f base = packVec16 m1 f base + (W16 ^ m1) * packVec16 m2 f (base + m1)
  | 0, m2, f, base => by simp [packVec16]
  | m1 + 1, m2, f, base => by
    have hadd : m1 + 1 + m2 = (m1 + m2) + 1 := by omega
    rw [hadd]
    dsimp [packVec16]
    rw [packVec16_split m1 m2 f (base + 1)]
    have hbase : base + 1 + m1 = base + (m1 + 1) := by omega
    rw [hbase, Nat.pow_succ]
    ring

lemma packVec16_lt_pow : ∀ (n : ℕ) (f : ℕ → ℕ) (base : ℕ),
    (∀ k < n, f (base + k) < W16) → packVec16 n f base < W16 ^ n
  | 0, _, _, _ => by simp [packVec16]
  | n + 1, f, base, h => by
    dsimp [packVec16]
    have h0 : f base < W16 := by simpa using h 0 (Nat.zero_lt_succ n)
    have ih := packVec16_lt_pow n f (base + 1) (fun k hk => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h (k + 1) (by omega))
    rw [Nat.pow_succ]
    have hmul : W16 * packVec16 n f (base + 1) + W16 ≤ W16 * (W16 ^ n) := by
      have h1 : packVec16 n f (base + 1) + 1 ≤ W16 ^ n := ih
      calc W16 * packVec16 n f (base + 1) + W16 = W16 * (packVec16 n f (base + 1) + 1) := by ring
        _ ≤ W16 * (W16 ^ n) := Nat.mul_le_mul_left W16 h1
    rw [mul_comm (W16 ^ n) W16]
    omega

lemma packVec16_mod_split (m1 m2 : ℕ) (f : ℕ → ℕ) (base : ℕ)
    (hb : ∀ k < m1 + m2, f (base + k) < W16) :
    (packVec16 (m1 + m2) f base) % (W16 ^ m1) = packVec16 m1 f base := by
  have hlt : packVec16 m1 f base < W16 ^ m1 :=
    packVec16_lt_pow m1 f base (fun k hk => hb k (by omega))
  rw [packVec16_split m1 m2 f base, mul_comm (W16 ^ m1), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hlt]

lemma packVec16_div_split (m1 m2 : ℕ) (f : ℕ → ℕ) (base : ℕ)
    (hb : ∀ k < m1 + m2, f (base + k) < W16) :
    (packVec16 (m1 + m2) f base) / (W16 ^ m1) = packVec16 m2 f (base + m1) := by
  have hlt : packVec16 m1 f base < W16 ^ m1 :=
    packVec16_lt_pow m1 f base (fun k hk => hb k (by omega))
  have hpos : 0 < W16 ^ m1 := Nat.pow_pos (by decide)
  rw [packVec16_split m1 m2 f base, mul_comm (W16 ^ m1), Nat.add_mul_div_right _ _ hpos,
      Nat.div_eq_of_lt hlt, zero_add]

lemma packVec16_two_mod (f : ℕ → ℕ) (base : ℕ) (hb : ∀ k < 2, f (base + k) < W16) :
    (packVec16 2 f base) % W16 = f base := by
  have h := packVec16_mod_split 1 1 f base hb
  simpa [packVec16] using h

lemma packVec16_two_div (f : ℕ → ℕ) (base : ℕ) (hb : ∀ k < 2, f (base + k) < W16) :
    (packVec16 2 f base) / W16 = f (base + 1) := by
  have h := packVec16_div_split 1 1 f base hb
  simpa [packVec16] using h

def vecSumZ (p q : ℕ → ℕ) (v : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | m + 1, base => ((p base : ℤ) - (q base : ℤ)) * v base + vecSumZ p q v m (base + 1)

lemma vecSumZ_split : ∀ (m1 m2 : ℕ) (p q : ℕ → ℕ) (v : ℕ → ℤ) (base : ℕ),
    vecSumZ p q v (m1 + m2) base = vecSumZ p q v m1 base + vecSumZ p q v m2 (base + m1)
  | 0, m2, p, q, v, base => by simp [vecSumZ]
  | m1 + 1, m2, p, q, v, base => by
    have hadd : m1 + 1 + m2 = (m1 + m2) + 1 := by omega
    rw [hadd]
    dsimp [vecSumZ]
    rw [vecSumZ_split m1 m2 p q v (base + 1)]
    have hbase : base + 1 + m1 = base + (m1 + 1) := by omega
    rw [hbase]; ring

lemma vecSumZ_congr : ∀ (m : ℕ) (p1 q1 p2 q2 : ℕ → ℕ) (v : ℕ → ℤ) (base : ℕ),
    (∀ k < m, ((p1 (base + k) : ℤ) - (q1 (base + k) : ℤ)) = ((p2 (base + k) : ℤ) - (q2 (base + k) : ℤ))) →
    vecSumZ p1 q1 v m base = vecSumZ p2 q2 v m base
  | 0, _, _, _, _, _, _, _ => rfl
  | m + 1, p1, q1, p2, q2, v, base, h => by
    dsimp [vecSumZ]
    have h0 := h 0 (Nat.zero_lt_succ m)
    simp only [Nat.add_zero] at h0
    have ih := vecSumZ_congr m p1 q1 p2 q2 v (base + 1) (fun k hk => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h (k + 1) (by omega))
    rw [h0, ih]

lemma vecSumZ_linear (mult : ℕ) : ∀ (m : ℕ) (p q pA qA : ℕ → ℕ) (v : ℕ → ℤ) (base : ℕ),
    vecSumZ (fun i => p i + mult * pA i) (fun i => q i + mult * qA i) v m base =
      vecSumZ p q v m base + (mult : ℤ) * vecSumZ pA qA v m base
  | 0, _, _, _, _, _, _ => by simp [vecSumZ]
  | m + 1, p, q, pA, qA, v, base => by
    dsimp [vecSumZ]
    rw [vecSumZ_linear mult m p q pA qA v (base + 1)]
    ring

lemma vecSumZ_zero : ∀ (m : ℕ) (v : ℕ → ℤ) (base : ℕ), vecSumZ (fun _ => 0) (fun _ => 0) v m base = 0
  | 0, _, _ => rfl
  | m + 1, v, base => by simp [vecSumZ, vecSumZ_zero m v (base + 1)]

lemma vecSumZ_scale (mult : ℕ) (m : ℕ) (p0 q0 : ℕ → ℕ) (v : ℕ → ℤ) (base : ℕ) :
    vecSumZ (fun i => mult * p0 i) (fun i => mult * q0 i) v m base =
      (mult : ℤ) * vecSumZ p0 q0 v m base := by
  have h := vecSumZ_linear mult m (fun _ => 0) (fun _ => 0) p0 q0 v base
  simpa [vecSumZ_zero m v base] using h

lemma vecSumZ_single_pos : ∀ (n base u : ℕ) (v : ℕ → ℤ), base ≤ u → u < base + n →
    vecSumZ (fun i => if i = u then 1 else 0) (fun _ => 0) v n base = v u
  | 0, _, _, _, _, hlt => by omega
  | n + 1, base, u, v, hle, hlt => by
    dsimp [vecSumZ]
    by_cases heq : base = u
    · subst heq
      have hz : vecSumZ (fun i => if i = base then 1 else 0) (fun _ => 0) v n (base + 1) = 0 := by
        rw [vecSumZ_congr n _ _ (fun _ => 0) (fun _ => 0) v (base + 1) (by intro k _; simp; omega),
            vecSumZ_zero]
      simp [hz]
    · rw [if_neg heq]; simp only [Nat.cast_zero, sub_self, zero_mul, zero_add]
      exact vecSumZ_single_pos n (base + 1) u v (by omega) (by omega)

lemma vecSumZ_single_neg : ∀ (n base u : ℕ) (v : ℕ → ℤ), base ≤ u → u < base + n →
    vecSumZ (fun _ => 0) (fun i => if i = u then 1 else 0) v n base = - v u
  | 0, _, _, _, _, hlt => by omega
  | n + 1, base, u, v, hle, hlt => by
    dsimp [vecSumZ]
    by_cases heq : base = u
    · subst heq
      have hz : vecSumZ (fun _ => 0) (fun i => if i = base then 1 else 0) v n (base + 1) = 0 := by
        rw [vecSumZ_congr n _ _ (fun _ => 0) (fun _ => 0) v (base + 1) (by intro k _; simp; omega),
            vecSumZ_zero]
      simp [hz]
    · rw [if_neg heq]; simp only [Nat.cast_zero, sub_self, zero_mul, zero_add]
      exact vecSumZ_single_neg n (base + 1) u v (by omega) (by omega)

lemma vecSumZ_cl (n : ℕ) (v : ℕ → ℤ) : ∀ (cl : List ℕ), cl.Nodup → (∀ u ∈ cl, u < n) →
    vecSumZ (fun i => if i ∈ cl then 1 else 0) (fun _ => 0) v n 0 = (cl.map v).sum
  | [], _, _ => by
    rw [vecSumZ_congr n _ _ (fun _ => 0) (fun _ => 0) v 0 (by simp), vecSumZ_zero]; simp
  | u :: us, hnd, hlt => by
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    have hu : u < n := hlt u List.mem_cons_self
    have hus : ∀ x ∈ us, x < n := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    have hlin := vecSumZ_linear 1 n (fun i => if i = u then 1 else 0) (fun _ => 0)
      (fun i => if i ∈ us then 1 else 0) (fun _ => 0) v 0
    have hcon : vecSumZ (fun i => if i ∈ u :: us then 1 else 0) (fun _ => 0) v n 0 =
        vecSumZ (fun i => (if i = u then 1 else 0) + 1 * (if i ∈ us then 1 else 0))
          (fun _ => 0 + 1 * 0) v n 0 := by
      apply vecSumZ_congr; intro k _; simp only [Nat.zero_add, one_mul]
      by_cases hku : k = u
      · subst hku; simp [hnot]
      · by_cases hkus : k ∈ us <;> simp [hku, hkus]
    rw [hcon, hlin, vecSumZ_single_pos n 0 u v (Nat.zero_le u) (by omega),
        vecSumZ_cl n v us hnd' hus]
    simp

lemma vecSumZ_eq_list_sum (f : ℕ → ℤ) (p q : ℕ → ℕ) (v : ℕ → ℤ) :
    ∀ (n : ℕ), (∀ k < n, ((p k : ℤ) - (q k : ℤ)) = f k) →
      vecSumZ p q v n 0 = ((List.range n).map (fun j => f j * v j)).sum
  | 0, _ => rfl
  | n + 1, h => by
    rw [vecSumZ_split n 1 p q v 0,
        vecSumZ_eq_list_sum f p q v n (fun k hk => h k (by omega))]
    dsimp [vecSumZ]
    rw [Nat.zero_add, h n (Nat.lt_succ_self n), List.range_succ, List.map_append, List.sum_append]
    simp

def buildInitVecs16 (w_in : List Nat) (wMul extraAdd t : Nat) : Nat → Nat → Nat × Nat × Nat
  | 0, _ => (0, 0, 0)
  | Nat.succ rem, u =>
    match buildInitVecs16 w_in wMul extraAdd t rem (Nat.add u 1) with
    | (pRest, nRest, mcRest) =>
      let posVal := Nat.add (Nat.mul wMul (maskWeightRec w_in u)) extraAdd
      let ls := laneShift16 u
      match Nat.ble t posVal with
      | true =>
        let d := Nat.sub posVal t
        (Nat.add pRest (Nat.mul d ls), nRest, match Nat.blt mcRest d with | true => d | false => mcRest)
      | false =>
        let d := Nat.sub t posVal
        (pRest, Nat.add nRest (Nat.mul d ls), match Nat.blt mcRest d with | true => d | false => mcRest)

lemma buildInitVecs16_spec (w_in : List ℕ) (wMul extraAdd t : ℕ) :
    ∀ (rem base : ℕ),
      let p0 (u : ℕ) : ℕ := (wMul * maskWeightRec w_in u + extraAdd) - t
      let q0 (u : ℕ) : ℕ := t - (wMul * maskWeightRec w_in u + extraAdd)
      let res := buildInitVecs16 w_in wMul extraAdd t rem base
      res.1 = (W16 ^ base) * packVec16 rem p0 base ∧
      res.2.1 = (W16 ^ base) * packVec16 rem q0 base ∧
      (∀ k < rem, p0 (base + k) ≤ res.2.2 ∧ q0 (base + k) ≤ res.2.2)
  | 0, base => by simp [buildInitVecs16, packVec16]
  | rem + 1, base => by
    have ih := buildInitVecs16_spec w_in wMul extraAdd t rem (base + 1)
    dsimp only at ih ⊢
    rcases hrec : buildInitVecs16 w_in wMul extraAdd t rem (base + 1) with ⟨pR, nR, mcR⟩
    rw [hrec] at ih
    dsimp only at ih
    dsimp only [buildInitVecs16]
    simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, hrec]
    set posVal := wMul * maskWeightRec w_in base + extraAdd
    have hls : laneShift16 base = W16 ^ base := laneShift16_eq_pow base
    cases hble : Nat.ble t posVal
    · dsimp only
      have hlt : posVal < t := by simp at hble; exact hble
      have hp0_z : posVal - t = 0 := by omega
      refine ⟨?_, ?_, ?_⟩
      · dsimp [packVec16]; rw [hp0_z, zero_add, ih.1, Nat.pow_succ]; ring
      · dsimp [packVec16]; rw [hls, ih.2.1, Nat.pow_succ]; ring
      · intro k hk
        cases k with
        | zero =>
          simp only [Nat.add_zero]
          cases hblt : Nat.blt mcR (t - posVal)
          · simp at hblt; dsimp only; omega
          · dsimp only; omega
        | succ k' =>
          have hprev := ih.2.2 k' (by omega)
          rw [show base + (k' + 1) = base + 1 + k' by omega]
          cases hblt : Nat.blt mcR (t - posVal)
          · exact hprev
          · simp at hblt; dsimp only; omega
    · dsimp only
      have hle : t ≤ posVal := by simp at hble; exact hble
      have hq0_z : t - posVal = 0 := by omega
      refine ⟨?_, ?_, ?_⟩
      · dsimp [packVec16]; rw [hls, ih.1, Nat.pow_succ]; ring
      · dsimp [packVec16]; rw [hq0_z, zero_add, ih.2.1, Nat.pow_succ]; ring
      · intro k hk
        cases k with
        | zero =>
          simp only [Nat.add_zero]
          cases hblt : Nat.blt mcR (posVal - t)
          · simp at hblt; dsimp only; omega
          · dsimp only; omega
        | succ k' =>
          have hprev := ih.2.2 k' (by omega)
          rw [show base + (k' + 1) = base + 1 + k' by omega]
          cases hblt : Nat.blt mcR (posVal - t)
          · exact hprev
          · simp at hblt; dsimp only; omega

inductive Sp16 where
  | leaf1
  | leaf2
  | leaf4
  | leaf8
  | node (wHalf mHalf fullMask emptyBias : Nat) (sub : Sp16)

def buildSp16 : Nat → Sp16
  | 0 => Sp16.leaf1
  | 1 => Sp16.leaf2
  | 2 => Sp16.leaf4
  | 3 => Sp16.leaf8
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ d))) =>
    let d3 := Nat.add d 3
    let halfLanes := Nat.pow 2 d3
    Sp16.node
      (Nat.pow 2 (Nat.mul 16 halfLanes))
      (Nat.pow 2 halfLanes)
      (Nat.sub (Nat.pow 2 (Nat.mul 2 halfLanes)) 1)
      (Nat.mul (Nat.mul 2 halfLanes) BIAS16)
      (buildSp16 d3)

def lane1 (zmBit omBit pd nd : Nat) : Nat :=
  match Nat.beq zmBit 1 with
  | true => BIAS16
  | false =>
    match Nat.beq omBit 1 with
    | true => Nat.sub (Nat.add BIAS16 pd) nd
    | false =>
      match Nat.blt pd nd with
      | true => Nat.sub (Nat.add BIAS16 pd) nd
      | false => BIAS16

def leaf4Helper (zm om p01 p23 n01 n23 : Nat) : Nat :=
  Nat.add
    (Nat.add
      (lane1 (Nat.mod zm 2) (Nat.mod om 2) (Nat.mod p01 W16) (Nat.mod n01 W16))
      (lane1 (Nat.mod (Nat.div zm 2) 2) (Nat.mod (Nat.div om 2) 2) (Nat.div p01 W16) (Nat.div n01 W16)))
    (Nat.add
      (lane1 (Nat.mod (Nat.div zm 4) 2) (Nat.mod (Nat.div om 4) 2) (Nat.mod p23 W16) (Nat.mod n23 W16))
      (lane1 (Nat.div zm 8) (Nat.div om 8) (Nat.div p23 W16) (Nat.div n23 W16)))

def leaf4From64 (zm om p64 n64 : Nat) : Nat :=
  match (Nat.beq zm 15 || (Nat.beq om 0 && Nat.beq n64 0)) with
  | true => 0x400000000
  | false => leaf4Helper zm om (Nat.mod p64 W32) (Nat.div p64 W32) (Nat.mod n64 W32) (Nat.div n64 W32)

def lbSwar16 (sp : Sp16) (zm om pr nr : Nat) : Nat :=
  match sp with
  | Sp16.leaf1 =>
    lane1 (Nat.mod zm 2) (Nat.mod om 2) (Nat.mod pr W16) (Nat.mod nr W16)
  | Sp16.leaf2 =>
    Nat.add
      (lane1 (Nat.mod zm 2) (Nat.mod om 2) (Nat.mod pr W16) (Nat.mod nr W16))
      (lane1 (Nat.div zm 2) (Nat.div om 2) (Nat.div pr W16) (Nat.div nr W16))
  | Sp16.leaf4 =>
    leaf4From64 zm om pr nr
  | Sp16.leaf8 =>
    match (Nat.beq zm 255 || (Nat.beq om 0 && Nat.beq nr 0)) with
    | true => 0x800000000
    | false =>
      Nat.add
        (leaf4From64 (Nat.mod zm 16) (Nat.mod om 16) (Nat.mod pr W64) (Nat.mod nr W64))
        (leaf4From64 (Nat.div zm 16) (Nat.div om 16) (Nat.div pr W64) (Nat.div nr W64))
  | Sp16.node wHalf mHalf fullMask emptyBias sub =>
    match (Nat.beq zm fullMask || (Nat.beq om 0 && Nat.beq nr 0)) with
    | true => emptyBias
    | false =>
      Nat.add
        (lbSwar16 sub (Nat.mod zm mHalf) (Nat.mod om mHalf) (Nat.mod pr wHalf) (Nat.mod nr wHalf))
        (lbSwar16 sub (Nat.div zm mHalf) (Nat.div om mHalf) (Nat.div pr wHalf) (Nat.div nr wHalf))

lemma lane1_sound {zmBit omBit pd nd : ℕ} {vb : ℤ}
    (hpd : pd < W16) (hnd : nd < W16)
    (hbit : vb = 0 ∨ vb = 1)
    (hz : zmBit = 1 → vb = 0) (ho : omBit = 1 → vb = 1) :
    (lane1 zmBit omBit pd nd : ℤ) - (BIAS16 : ℤ) ≤ ((pd : ℤ) - (nd : ℤ)) * vb := by
  unfold lane1
  have hW : W16 = 65536 := rfl
  have hB : BIAS16 = 4294967296 := rfl
  cases h1 : Nat.beq zmBit 1
  · cases h2 : Nat.beq omBit 1
    · cases h3 : Nat.blt pd nd
      · simp at h3
        rcases hbit with rfl | rfl <;> (change (BIAS16 : ℤ) - (BIAS16 : ℤ) ≤ _; omega)
      · simp at h3
        change ((((BIAS16 + pd - nd : ℕ) : ℤ)) - (BIAS16 : ℤ)) ≤ _
        rcases hbit with rfl | rfl <;> omega
    · rw [ho (Nat.beq_eq.mp h2)]
      change ((((BIAS16 + pd - nd : ℕ) : ℤ)) - (BIAS16 : ℤ)) ≤ _
      omega
  · rw [hz (Nat.beq_eq.mp h1)]
    change (BIAS16 : ℤ) - (BIAS16 : ℤ) ≤ _
    omega

lemma testBit_of_div_pow_eq_one {m k : ℕ} (h : m / (2 ^ k) = 1) : m.testBit k = true := by
  rw [← Nat.shiftRight_eq_div_pow] at h
  have ht : (m >>> k).testBit 0 = true := by rw [h]; rfl
  rw [Nat.testBit_shiftRight, Nat.add_zero] at ht
  exact ht

lemma testBit_of_div_pow_mod_two_eq_one {m k : ℕ} (h : (m / (2 ^ k)) % 2 = 1) : m.testBit k = true := by
  rw [← Nat.shiftRight_eq_div_pow] at h
  have ht : (m >>> k).testBit 0 = true := by rw [Nat.testBit_zero, h]; rfl
  rw [Nat.testBit_shiftRight, Nat.add_zero] at ht
  exact ht

lemma shortcut_sound (m : ℕ) (p q : ℕ → ℕ) (v : ℕ → ℤ) (base zm om : ℕ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (hz : ∀ k < m, zm.testBit k = true → v (base + k) = 0)
    (hshort : (Nat.beq zm (2 ^ m - 1) || (Nat.beq om 0 && Nat.beq (packVec16 m q base) 0)) = true) :
    0 ≤ vecSumZ p q v m base := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at hshort
  have nonneg_of_terms : (∀ k < m, 0 ≤ ((p (base + k) : ℤ) - (q (base + k) : ℤ)) * v (base + k)) →
      0 ≤ vecSumZ p q v m base := by
    clear hshort hz
    induction m generalizing base with
    | zero => intro _; simp [vecSumZ]
    | succ m' ih =>
      intro ht; dsimp [vecSumZ]
      have h0 := ht 0 (Nat.zero_lt_succ m'); simp only [Nat.add_zero] at h0
      have hrest := ih (base + 1) (fun k hk => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using ht (k + 1) (by omega))
      linarith
  apply nonneg_of_terms
  intro k hk
  rcases hshort with hzm | ⟨_, hnr⟩
  · subst hzm
    have htb : (2 ^ m - 1).testBit k = true := by simp [Nat.testBit_two_pow_sub_one, hk]
    rw [hz k hk htb]; simp
  · have hqk := packVec16_eq_zero_iff m q base hnr k hk
    rw [hqk]
    rcases bit (base + k) with hv | hv <;> (rw [hv]; omega)

lemma leaf4From64_sound (p q : ℕ → ℕ) (v : ℕ → ℤ) (base zm om : ℕ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (hz : ∀ k < 4, zm.testBit k = true → v (base + k) = 0)
    (ho : ∀ k < 4, om.testBit k = true → v (base + k) = 1)
    (hp : ∀ k < 4, p (base + k) < W16)
    (hq : ∀ k < 4, q (base + k) < W16) :
    (leaf4From64 zm om (packVec16 4 p base) (packVec16 4 q base) : ℤ) - 4 * (BIAS16 : ℤ) ≤
      vecSumZ p q v 4 base := by
  unfold leaf4From64
  cases hsh : (Nat.beq zm 15 || (Nat.beq om 0 && Nat.beq (packVec16 4 q base) 0))
  · dsimp only
    simp only [nat_mod_eq, nat_div_eq]
    have hW32 : W32 = W16 ^ 2 := by decide
    have hp4 : ∀ k < 2 + 2, p (base + k) < W16 := hp
    have hq4 : ∀ k < 2 + 2, q (base + k) < W16 := hq
    rw [hW32, show (4 : ℕ) = 2 + 2 from rfl,
        packVec16_mod_split 2 2 p base hp4, packVec16_div_split 2 2 p base hp4,
        packVec16_mod_split 2 2 q base hq4, packVec16_div_split 2 2 q base hq4]
    unfold leaf4Helper
    simp only [nat_add_eq, nat_mod_eq, nat_div_eq]
    have hp2a : ∀ k < 2, p (base + k) < W16 := fun k hk => hp k (by omega)
    have hp2b : ∀ k < 2, p (base + 2 + k) < W16 := fun k hk => by
      simpa [Nat.add_assoc] using hp (2 + k) (by omega)
    have hq2a : ∀ k < 2, q (base + k) < W16 := fun k hk => hq k (by omega)
    have hq2b : ∀ k < 2, q (base + 2 + k) < W16 := fun k hk => by
      simpa [Nat.add_assoc] using hq (2 + k) (by omega)
    rw [packVec16_two_mod p base hp2a, packVec16_two_div p base hp2a,
        packVec16_two_mod p (base + 2) hp2b, packVec16_two_div p (base + 2) hp2b,
        packVec16_two_mod q base hq2a, packVec16_two_div q base hq2a,
        packVec16_two_mod q (base + 2) hq2b, packVec16_two_div q (base + 2) hq2b]
    have l0 := lane1_sound (by simpa using hp 0 (by omega)) (by simpa using hq 0 (by omega)) (bit base)
      (fun h1 => by simpa using hz 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
      (fun h1 => by simpa using ho 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
    have l1 := lane1_sound (hp 1 (by omega)) (hq 1 (by omega)) (bit (base + 1))
      (fun h1 => hz 1 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 1) (by simpa using h1)))
      (fun h1 => ho 1 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 1) (by simpa using h1)))
    have l2 := lane1_sound (hp 2 (by omega)) (hq 2 (by omega)) (bit (base + 2))
      (fun h1 => hz 2 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 2) (by simpa using h1)))
      (fun h1 => ho 2 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 2) (by simpa using h1)))
    have l3 := lane1_sound (by simpa [Nat.add_assoc] using hp 3 (by omega))
      (by simpa [Nat.add_assoc] using hq 3 (by omega)) (bit (base + 2 + 1))
      (fun h1 => by simpa [Nat.add_assoc] using hz 3 (by omega) (testBit_of_div_pow_eq_one (k := 3) (by simpa using h1)))
      (fun h1 => by simpa [Nat.add_assoc] using ho 3 (by omega) (testBit_of_div_pow_eq_one (k := 3) (by simpa using h1)))
    dsimp [vecSumZ]
    have ha3 : base + 1 + 1 + 1 = base + 2 + 1 := by omega
    have ha2 : base + 1 + 1 = base + 2 := by omega
    rw [ha3, ha2]
    linarith
  · dsimp only
    have h4B : ((0x400000000 : ℕ) : ℤ) - 4 * (BIAS16 : ℤ) = 0 := by decide
    rw [h4B]
    exact shortcut_sound 4 p q v base zm om bit hz hsh

lemma lbSwar16_sound (p q : ℕ → ℕ) (v : ℕ → ℤ) (bit : ∀ i, v i = 0 ∨ v i = 1) :
    ∀ (d : ℕ) (base zm om : ℕ),
      (∀ k < 2 ^ d, zm.testBit k = true → v (base + k) = 0) →
      (∀ k < 2 ^ d, om.testBit k = true → v (base + k) = 1) →
      (∀ k < 2 ^ d, p (base + k) < W16) →
      (∀ k < 2 ^ d, q (base + k) < W16) →
      (lbSwar16 (buildSp16 d) zm om (packVec16 (2 ^ d) p base) (packVec16 (2 ^ d) q base) : ℤ) -
        ((2 ^ d : ℕ) : ℤ) * (BIAS16 : ℤ) ≤ vecSumZ p q v (2 ^ d) base
  | 0, base, zm, om, hz, ho, hp, hq => by
    dsimp [buildSp16, lbSwar16, packVec16, vecSumZ]
    simp only [add_zero, one_mul]
    have hp0 : p base < W16 := by simpa using hp 0 (by omega)
    have hq0 : q base < W16 := by simpa using hq 0 (by omega)
    rw [Nat.mod_eq_of_lt hp0, Nat.mod_eq_of_lt hq0]
    exact lane1_sound hp0 hq0 (bit base)
      (fun h1 => by simpa using hz 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
      (fun h1 => by simpa using ho 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
  | 1, base, zm, om, hz, ho, hp, hq => by
    dsimp [buildSp16, lbSwar16]
    rw [packVec16_two_mod p base hp, packVec16_two_div p base hp,
        packVec16_two_mod q base hq, packVec16_two_div q base hq]
    have l0 := lane1_sound (by simpa using hp 0 (by omega)) (by simpa using hq 0 (by omega)) (bit base)
      (fun h1 => by simpa using hz 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
      (fun h1 => by simpa using ho 0 (by omega) (testBit_of_div_pow_mod_two_eq_one (k := 0) (by simpa using h1)))
    have l1 := lane1_sound (hp 1 (by omega)) (hq 1 (by omega)) (bit (base + 1))
      (fun h1 => hz 1 (by omega) (testBit_of_div_pow_eq_one (k := 1) (by simpa using h1)))
      (fun h1 => ho 1 (by omega) (testBit_of_div_pow_eq_one (k := 1) (by simpa using h1)))
    dsimp [vecSumZ]; linarith
  | 2, base, zm, om, hz, ho, hp, hq => by
    simpa [buildSp16, lbSwar16] using leaf4From64_sound p q v base zm om bit hz ho hp hq
  | 3, base, zm, om, hz, ho, hp, hq => by
    have hb3 : buildSp16 3 = Sp16.leaf8 := rfl
    rw [hb3, show 2 ^ 3 = 8 from rfl]
    dsimp only [lbSwar16]
    cases hsh : (Nat.beq zm 255 || (Nat.beq om 0 && Nat.beq (packVec16 8 q base) 0))
    · dsimp only
      simp only [nat_add_eq, nat_mod_eq, nat_div_eq]
      have hW64 : W64 = W16 ^ 4 := by decide
      have hp8 : ∀ k < 4 + 4, p (base + k) < W16 := hp
      have hq8 : ∀ k < 4 + 4, q (base + k) < W16 := hq
      rw [hW64, show (8 : ℕ) = 4 + 4 from rfl,
          packVec16_mod_split 4 4 p base hp8, packVec16_div_split 4 4 p base hp8,
          packVec16_mod_split 4 4 q base hq8, packVec16_div_split 4 4 q base hq8,
          vecSumZ_split 4 4 p q v base]
      have sL := leaf4From64_sound p q v base (zm % 16) (om % 16) bit
        (fun k hk htb => hz k (by omega) (by rw [show (16 : ℕ) = 2 ^ 4 by decide, Nat.testBit_mod_two_pow] at htb; simpa [hk] using htb))
        (fun k hk htb => ho k (by omega) (by rw [show (16 : ℕ) = 2 ^ 4 by decide, Nat.testBit_mod_two_pow] at htb; simpa [hk] using htb))
        (fun k hk => hp k (by omega)) (fun k hk => hq k (by omega))
      have sR := leaf4From64_sound p q v (base + 4) (zm / 16) (om / 16) bit
        (fun k hk htb => by
          rw [show (16 : ℕ) = 2 ^ 4 by decide, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at htb
          simpa [Nat.add_assoc] using hz (4 + k) (by omega) htb)
        (fun k hk htb => by
          rw [show (16 : ℕ) = 2 ^ 4 by decide, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at htb
          simpa [Nat.add_assoc] using ho (4 + k) (by omega) htb)
        (fun k hk => by simpa [Nat.add_assoc] using hp (4 + k) (by omega))
        (fun k hk => by simpa [Nat.add_assoc] using hq (4 + k) (by omega))
      push_cast; linarith
    · dsimp only
      have h8B : ((0x800000000 : ℕ) : ℤ) - ((8 : ℕ) : ℤ) * (BIAS16 : ℤ) = 0 := by decide
      rw [h8B]; exact shortcut_sound 8 p q v base zm om bit hz hsh
  | d + 4, base, zm, om, hz, ho, hp, hq => by
    dsimp only [buildSp16, lbSwar16]
    simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq]
    set m := 2 ^ (d + 3)
    have hm2 : 2 * m = 2 ^ (d + 4) := by
      change 2 * 2 ^ (d + 3) = 2 ^ ((d + 3) + 1); rw [Nat.pow_succ]; ring
    have hwH : 2 ^ (16 * m) = W16 ^ m := by
      change 2 ^ (16 * m) = (2 ^ 16) ^ m; rw [← Nat.pow_mul]
    rw [hm2, hwH]
    cases hsh : (Nat.beq zm (2 ^ (2 ^ (d + 4)) - 1) ||
                 (Nat.beq om 0 && Nat.beq (packVec16 (2 ^ (d + 4)) q base) 0))
    · dsimp only
      simp only [nat_mod_eq, nat_div_eq]
      have hpow_add : 2 ^ (d + 4) = m + m := by
        change 2 ^ ((d + 3) + 1) = m + m; rw [Nat.pow_succ]; omega
      have hp' : ∀ k < m + m, p (base + k) < W16 := by rwa [← hpow_add]
      have hq' : ∀ k < m + m, q (base + k) < W16 := by rwa [← hpow_add]
      rw [hpow_add, packVec16_mod_split m m p base hp', packVec16_div_split m m p base hp',
          packVec16_mod_split m m q base hq', packVec16_div_split m m q base hq',
          vecSumZ_split m m p q v base]
      have ihL := lbSwar16_sound p q v bit (d + 3) base (zm % (2 ^ m)) (om % (2 ^ m))
        (fun k hk htb => hz k (by omega) ((Eq.mp (Bool.and_eq_true _ _) (by rwa [Nat.testBit_mod_two_pow] at htb)).2))
        (fun k hk htb => ho k (by omega) ((Eq.mp (Bool.and_eq_true _ _) (by rwa [Nat.testBit_mod_two_pow] at htb)).2))
        (fun k hk => hp k (by omega)) (fun k hk => hq k (by omega))
      have ihR := lbSwar16_sound p q v bit (d + 3) (base + m) (zm / (2 ^ m)) (om / (2 ^ m))
        (fun k hk htb => by
          rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at htb
          simpa [Nat.add_assoc] using hz (m + k) (by omega) htb)
        (fun k hk htb => by
          rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight] at htb
          simpa [Nat.add_assoc] using ho (m + k) (by omega) htb)
        (fun k hk => by simpa [Nat.add_assoc] using hp (m + k) (by omega))
        (fun k hk => by simpa [Nat.add_assoc] using hq (m + k) (by omega))
      push_cast; linarith
    · dsimp only
      have heqB : ((2 ^ (d + 4) * BIAS16 : ℕ) : ℤ) - ((2 ^ (d + 4) : ℕ) : ℤ) * (BIAS16 : ℤ) = 0 := by
        push_cast; ring
      rw [heqB]
      exact shortcut_sound (2 ^ (d + 4)) p q v base zm om bit hz hsh

def pow32Shift : Nat → Nat
  | 0 => 0x100000000
  | 1 => 0x10000000000000000
  | 2 => Nat.pow 2 128
  | 3 => Nat.pow 2 256
  | 4 => Nat.pow 2 512
  | 5 => Nat.pow 2 1024
  | d => Nat.pow 2 (Nat.mul 32 (Nat.pow 2 d))

def split32Aux : Nat → Nat → List Nat → List Nat
  | 0, s, acc => Nat.mod s W32 :: acc
  | Nat.succ d, s, acc =>
    let p := pow32Shift d
    split32Aux d (Nat.mod s p) (split32Aux d (Nat.div s p) acc)

def split32Trim : Nat → Nat → List Nat → List Nat
  | 0, s, acc => Nat.mod s W32 :: acc
  | Nat.succ d, s, acc =>
    let p := pow32Shift d
    let hi := Nat.div s p
    match (Nat.beq hi 0 && acc.isEmpty) with
    | true => split32Trim d s []
    | false => split32Trim d (Nat.mod s p) (split32Trim d hi acc)

def chunksToWords32 : List Nat → List Nat
  | [] => []
  | [last] => split32Trim 6 last []
  | c :: cs => split32Aux 6 c (chunksToWords32 cs)

inductive B32 where
  | mk (buf av : Nat) (ws : List Nat)

def ensure30 : B32 → B32
  | B32.mk buf av ws =>
    match Nat.blt av 30 with
    | false => B32.mk buf av ws
    | true =>
      match ws with
      | [] => B32.mk buf 32 []
      | w :: ws' => B32.mk (Nat.add buf (Nat.mul w (Nat.pow 2 av))) (Nat.add av 32) ws'

def readBits32 (nbits : Nat) (st : B32) : Nat × B32 :=
  match Nat.beq nbits 0 with
  | true => (0, st)
  | false =>
    let p := Nat.pow 2 nbits
    match ensure30 st with
    | B32.mk b1 a1 w1 => (Nat.mod b1 p, B32.mk (Nat.div b1 p) (Nat.sub a1 nbits) w1)

def readVint32 (st : B32) : Nat × B32 :=
  match ensure30 st with
  | B32.mk b1 a1 w1 =>
    let lo2 := Nat.mod b1 4
    match Nat.beq (Nat.mod lo2 2) 1 with
    | true => (Nat.mod (Nat.div b1 2) 16, B32.mk (Nat.div b1 32) (Nat.sub a1 5) w1)
    | false =>
      match Nat.beq lo2 2 with
      | true => (Nat.add 16 (Nat.mod (Nat.div b1 4) 256), B32.mk (Nat.div b1 1024) (Nat.sub a1 10) w1)
      | false => (Nat.mod (Nat.div b1 4) 16384, B32.mk (Nat.div b1 65536) (Nat.sub a1 16) w1)

def readNatList32 (nbits : Nat) : Nat → B32 → List Nat × B32
  | 0, st => ([], st)
  | Nat.succ cnt, st =>
    match readBits32 nbits st with
    | (x, st1) =>
      match readNatList32 nbits cnt st1 with
      | (xs, st2) => (x :: xs, st2)

inductive SwarCut where
  | mk (posVec negVec rhsAdd : Nat)

inductive CutRope4 where
  | nil
  | cons (c : SwarCut) (n1 n4 n16 n64 : CutRope4)

def ropeDrop1 : Nat → CutRope4 → CutRope4
  | 0, r => r
  | Nat.succ k, r => match r with | CutRope4.nil => CutRope4.nil | CutRope4.cons _ n1 _ _ _ => ropeDrop1 k n1

def ropeDrop4 : Nat → CutRope4 → CutRope4
  | 0, r => r
  | Nat.succ k, r => match r with | CutRope4.nil => CutRope4.nil | CutRope4.cons _ _ n4 _ _ => ropeDrop4 k n4

def ropeDrop16 : Nat → CutRope4 → CutRope4
  | 0, r => r
  | Nat.succ k, r => match r with | CutRope4.nil => CutRope4.nil | CutRope4.cons _ _ _ n16 _ => ropeDrop16 k n16

def ropeDrop64 : Nat → CutRope4 → CutRope4
  | 0, r => r
  | Nat.succ k, r => match r with | CutRope4.nil => CutRope4.nil | CutRope4.cons _ _ _ _ n64 => ropeDrop64 k n64

def buildCutRope4 : List SwarCut → CutRope4
  | [] => CutRope4.nil
  | c :: cs =>
    let r1 := buildCutRope4 cs
    let r4 := ropeDrop1 3 r1
    let r16 := ropeDrop4 3 r4
    let r64 := ropeDrop16 3 r16
    CutRope4.cons c r1 r4 r16 r64

def ValidSwarCut (n : ℕ) (v : ℕ → ℤ) : SwarCut → Prop
  | SwarCut.mk pv nv ra =>
    ∃ pA qA : ℕ → ℕ,
      pv = packVec16 n pA 0 ∧
      nv = packVec16 n qA 0 ∧
      (∀ k < n, pA k ≤ 2 ∧ qA k ≤ 2) ∧
      vecSumZ pA qA v n 0 ≤ (ra : ℤ)

def AllRope (P : SwarCut → Prop) : CutRope4 → Prop
  | CutRope4.nil => True
  | CutRope4.cons c n1 n4 n16 n64 =>
    P c ∧ AllRope P n1 ∧ AllRope P n4 ∧ AllRope P n16 ∧ AllRope P n64

lemma ropeDrop1_all {P : SwarCut → Prop} : ∀ (k : ℕ) {r : CutRope4}, AllRope P r → AllRope P (ropeDrop1 k r)
  | 0, _, h => h
  | _ + 1, CutRope4.nil, _ => trivial
  | k + 1, CutRope4.cons _ _ _ _ _, h => ropeDrop1_all k h.2.1

lemma ropeDrop4_all {P : SwarCut → Prop} : ∀ (k : ℕ) {r : CutRope4}, AllRope P r → AllRope P (ropeDrop4 k r)
  | 0, _, h => h
  | _ + 1, CutRope4.nil, _ => trivial
  | k + 1, CutRope4.cons _ _ _ _ _, h => ropeDrop4_all k h.2.2.1

lemma ropeDrop16_all {P : SwarCut → Prop} : ∀ (k : ℕ) {r : CutRope4}, AllRope P r → AllRope P (ropeDrop16 k r)
  | 0, _, h => h
  | _ + 1, CutRope4.nil, _ => trivial
  | k + 1, CutRope4.cons _ _ _ _ _, h => ropeDrop16_all k h.2.2.2.1

lemma ropeDrop64_all {P : SwarCut → Prop} : ∀ (k : ℕ) {r : CutRope4}, AllRope P r → AllRope P (ropeDrop64 k r)
  | 0, _, h => h
  | _ + 1, CutRope4.nil, _ => trivial
  | k + 1, CutRope4.cons _ _ _ _ _, h => ropeDrop64_all k h.2.2.2.2

lemma buildCutRope4_all (P : SwarCut → Prop) : ∀ (cs : List SwarCut), (∀ c ∈ cs, P c) → AllRope P (buildCutRope4 cs)
  | [], _ => trivial
  | c :: cs, h => by
    have hr1 := buildCutRope4_all P cs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨h c List.mem_cons_self, hr1, ropeDrop1_all 3 hr1, ropeDrop4_all 3 (ropeDrop1_all 3 hr1),
      ropeDrop16_all 3 (ropeDrop4_all 3 (ropeDrop1_all 3 hr1))⟩

def readCutsLoop (b mbits n2b : Nat) (pArr : Arr8 Nat) (clArr : Arr8 (List Nat)) :
    Nat → B32 → Option (List SwarCut × B32)
  | 0, st => some ([], st)
  | Nat.succ cnt, st0 =>
    match readBits32 2 st0 with
    | (tk, st1) =>
      match Nat.beq tk 0 with
      | true =>
        match readBits32 b st1 with
        | (i, st2) =>
          match readBits32 b st2 with
          | (j, st3) =>
            let ij := Nat.lor i j
            match (Nat.blt i n2b && Nat.blt j n2b && Nat.blt ij n2b) with
            | true =>
              match readCutsLoop b mbits n2b pArr clArr cnt st3 with
              | none => none
              | some (cs, st') =>
                some (SwarCut.mk (Nat.add (laneShift16 i) (laneShift16 j)) (laneShift16 ij) 1 :: cs, st')
            | false => none
      | false =>
        match Nat.beq tk 1 with
        | true =>
          match readBits32 mbits st1 with
          | (mIdx, st2) =>
            match readBits32 b st2 with
            | (i, st3) =>
              match getArr8? pArr mIdx with
              | none => none
              | some m =>
                let im := Nat.lor i m
                match (Nat.blt i n2b && Nat.blt im n2b) with
                | true =>
                  match readCutsLoop b mbits n2b pArr clArr cnt st3 with
                  | none => none
                  | some (cs, st') =>
                    some (SwarCut.mk (laneShift16 i) (laneShift16 im) 0 :: cs, st')
                | false => none
        | false =>
          match Nat.beq tk 2 with
          | false => none
          | true =>
            match readVint32 st1 with
            | (clIdx, st2) =>
              match getArr8? clArr clIdx with
              | none => none
              | some cl =>
                match (Nat.ble 1 cl.length && nodupNat cl && listAll (fun x => Nat.blt x n2b) cl) with
                | true =>
                  match readCutsLoop b mbits n2b pArr clArr cnt st2 with
                  | none => none
                  | some (cs, st') =>
                    some (SwarCut.mk (sumLaneShifts16 cl) 0 (Nat.sub cl.length 1) :: cs, st')
                | false => none

lemma valid_join_cut {n i j : ℕ} {v : ℕ → ℤ}
    (hi : i < n) (hj : j < n) (hij : (i ||| j) < n)
    (hjoin : v i + v j - v (i ||| j) ≤ 1) :
    ValidSwarCut n v (SwarCut.mk (Nat.add (laneShift16 i) (laneShift16 j)) (laneShift16 (Nat.lor i j)) 1) := by
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0),
          fun k => if k = (i ||| j) then 1 else 0, ?_, ?_, ?_, ?_⟩
  · change laneShift16 i + laneShift16 j = _
    rw [laneShift16_eq_pow, laneShift16_eq_pow,
        ← Nat.sub_zero i, ← packVec16_single n 0 i (Nat.zero_le _) (by omega), Nat.sub_zero,
        ← Nat.sub_zero j, ← packVec16_single n 0 j (Nat.zero_le _) (by omega), Nat.sub_zero,
        packVec16_add]
  · change laneShift16 (i ||| j) = _
    rw [laneShift16_eq_pow, ← Nat.sub_zero (i ||| j),
        ← packVec16_single n 0 (i ||| j) (Nat.zero_le _) (by omega), Nat.sub_zero]
  · intro k _; dsimp only; split_ifs <;> omega
  · have h1 := vecSumZ_linear 1 n (fun k => if k = i then 1 else 0) (fun _ => 0)
      (fun k => if k = j then 1 else 0) (fun _ => 0) v 0
    have h2 := vecSumZ_linear 1 n (fun k => (if k = i then 1 else 0) + 1 * (if k = j then 1 else 0)) (fun _ => 0)
      (fun _ => 0) (fun k => if k = (i ||| j) then 1 else 0) v 0
    have hcon : vecSumZ (fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0))
        (fun k => if k = (i ||| j) then 1 else 0) v n 0 =
      vecSumZ (fun k => ((if k = i then 1 else 0) + 1 * (if k = j then 1 else 0)) + 1 * 0)
        (fun k => 0 + 1 * (if k = (i ||| j) then 1 else 0)) v n 0 := by
      apply vecSumZ_congr; intro k _; simp
    rw [hcon, h2, h1,
        vecSumZ_single_pos n 0 i v (Nat.zero_le _) (by omega),
        vecSumZ_single_pos n 0 j v (Nat.zero_le _) (by omega),
        vecSumZ_single_neg n 0 (i ||| j) v (Nat.zero_le _) (by omega)]
    push_cast; linarith

lemma valid_force_cut {n i m : ℕ} {v : ℕ → ℤ}
    (hi : i < n) (him : (i ||| m) < n)
    (hforce : v i ≤ v (i ||| m)) :
    ValidSwarCut n v (SwarCut.mk (laneShift16 i) (laneShift16 (Nat.lor i m)) 0) := by
  refine ⟨fun k => if k = i then 1 else 0, fun k => if k = (i ||| m) then 1 else 0, ?_, ?_, ?_, ?_⟩
  · rw [laneShift16_eq_pow, ← Nat.sub_zero i,
        ← packVec16_single n 0 i (Nat.zero_le _) (by omega), Nat.sub_zero]
  · change laneShift16 (i ||| m) = _
    rw [laneShift16_eq_pow, ← Nat.sub_zero (i ||| m),
        ← packVec16_single n 0 (i ||| m) (Nat.zero_le _) (by omega), Nat.sub_zero]
  · intro k _; dsimp only; split_ifs <;> omega
  · have hlin := vecSumZ_linear 1 n (fun k => if k = i then 1 else 0) (fun _ => 0)
      (fun _ => 0) (fun k => if k = (i ||| m) then 1 else 0) v 0
    have hcon : vecSumZ (fun k => if k = i then 1 else 0) (fun k => if k = (i ||| m) then 1 else 0) v n 0 =
      vecSumZ (fun k => (if k = i then 1 else 0) + 1 * 0)
        (fun k => 0 + 1 * (if k = (i ||| m) then 1 else 0)) v n 0 := by
      apply vecSumZ_congr; intro k _; simp
    rw [hcon, hlin,
        vecSumZ_single_pos n 0 i v (Nat.zero_le _) (by omega),
        vecSumZ_single_neg n 0 (i ||| m) v (Nat.zero_le _) (by omega)]
    push_cast; linarith

lemma valid_excl_cut {n : ℕ} {cl : List ℕ} {v : ℕ → ℤ}
    (hlen : 1 ≤ cl.length) (hnd : cl.Nodup) (hbnd : ∀ x ∈ cl, x < n)
    (hexcl : (cl.map v).sum ≤ (cl.length : ℤ) - 1) :
    ValidSwarCut n v (SwarCut.mk (sumLaneShifts16 cl) 0 (Nat.sub cl.length 1)) := by
  refine ⟨fun k => if k ∈ cl then 1 else 0, fun _ => 0,
    sumLaneShifts16_eq n cl hnd hbnd, (packVec16_zero n 0).symm, ?_, ?_⟩
  · intro k _; dsimp only; split_ifs <;> omega
  · rw [vecSumZ_cl n v cl hnd hbnd]
    change (cl.map v).sum ≤ (((cl.length - 1 : ℕ) : ℤ))
    omega

lemma readCutsLoop_sound (b mbits : ℕ) (P_cl : List ℕ) (cls : List (List ℕ)) (v : ℕ → ℤ)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (force : ∀ m ∈ P_cl, ∀ i, v i ≤ v (i ||| m))
    (excl : ∀ cl ∈ cls, (cl.map v).sum ≤ (cl.length : ℤ) - 1) :
    ∀ (cnt : ℕ) (st0 : B32) (cuts : List SwarCut) (st' : B32),
      readCutsLoop b mbits (Nat.pow 2 b) (listToArr8 P_cl) (listToArr8 cls) cnt st0 = some (cuts, st') →
      ∀ c ∈ cuts, ValidSwarCut (2 ^ b) v c
  | 0, _, cuts, _, hok => by
    simp only [readCutsLoop, Option.some.injEq, Prod.mk.injEq] at hok
    rcases hok with ⟨rfl, _⟩; intro _ h; cases h
  | cnt + 1, st0, cuts, st', hok => by
    dsimp only [readCutsLoop] at hok
    set r1 := readBits32 2 st0
    cases htk0 : Nat.beq r1.1 0
    · rw [htk0] at hok; dsimp only at hok
      cases htk1 : Nat.beq r1.1 1
      · rw [htk1] at hok; dsimp only at hok
        cases htk2 : Nat.beq r1.1 2
        · rw [htk2] at hok; cases hok
        · rw [htk2] at hok; dsimp only at hok
          set rv := readVint32 r1.2
          cases hcl : getArr8? (listToArr8 cls) rv.1 with
          | none => rw [hcl] at hok; cases hok
          | some cl =>
            rw [hcl] at hok; dsimp only at hok
            cases hcond : (Nat.ble 1 cl.length && nodupNat cl && listAll (fun x => Nat.blt x (Nat.pow 2 b)) cl)
            · rw [hcond] at hok; cases hok
            · rw [hcond] at hok; dsimp only at hok
              cases hrec : readCutsLoop b mbits (Nat.pow 2 b) (listToArr8 P_cl) (listToArr8 cls) cnt rv.2 with
              | none => rw [hrec] at hok; cases hok
              | some p =>
                rw [hrec] at hok; simp only [Option.some.injEq, Prod.mk.injEq] at hok
                rcases hok with ⟨rfl, rfl⟩
                simp only [Bool.and_eq_true, Nat.ble_eq, listAll_iff, Nat.blt_eq, nat_pow_eq] at hcond
                intro c hc
                rcases List.mem_cons.mp hc with rfl | hmem
                · exact valid_excl_cut hcond.1.1 (nodupNat_sound cl hcond.1.2) hcond.2
                    (excl cl (getArr8?_mem cls rv.1 cl hcl))
                · exact readCutsLoop_sound b mbits P_cl cls v join force excl cnt rv.2 p.1 p.2 hrec c hmem
      · rw [htk1] at hok; dsimp only at hok
        set rm := readBits32 mbits r1.2
        set ri := readBits32 b rm.2
        cases hm : getArr8? (listToArr8 P_cl) rm.1 with
        | none => rw [hm] at hok; cases hok
        | some m =>
          rw [hm] at hok; dsimp only at hok
          cases hcond : (Nat.blt ri.1 (Nat.pow 2 b) && Nat.blt (Nat.lor ri.1 m) (Nat.pow 2 b))
          · rw [hcond] at hok; cases hok
          · rw [hcond] at hok; dsimp only at hok
            cases hrec : readCutsLoop b mbits (Nat.pow 2 b) (listToArr8 P_cl) (listToArr8 cls) cnt ri.2 with
            | none => rw [hrec] at hok; cases hok
            | some p =>
              rw [hrec] at hok; simp only [Option.some.injEq, Prod.mk.injEq] at hok
              rcases hok with ⟨rfl, rfl⟩
              simp only [Bool.and_eq_true, Nat.blt_eq, nat_pow_eq, nat_lor_eq] at hcond
              intro c hc
              rcases List.mem_cons.mp hc with rfl | hmem
              · exact valid_force_cut hcond.1 hcond.2 (force m (getArr8?_mem P_cl rm.1 m hm) ri.1)
              · exact readCutsLoop_sound b mbits P_cl cls v join force excl cnt ri.2 p.1 p.2 hrec c hmem
    · rw [htk0] at hok; dsimp only at hok
      set ri := readBits32 b r1.2
      set rj := readBits32 b ri.2
      cases hcond : (Nat.blt ri.1 (Nat.pow 2 b) && Nat.blt rj.1 (Nat.pow 2 b) && Nat.blt (Nat.lor ri.1 rj.1) (Nat.pow 2 b))
      · rw [hcond] at hok; cases hok
      · rw [hcond] at hok; dsimp only at hok
        cases hrec : readCutsLoop b mbits (Nat.pow 2 b) (listToArr8 P_cl) (listToArr8 cls) cnt rj.2 with
        | none => rw [hrec] at hok; cases hok
        | some p =>
          rw [hrec] at hok; simp only [Option.some.injEq, Prod.mk.injEq] at hok
          rcases hok with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, Nat.blt_eq, nat_pow_eq, nat_lor_eq] at hcond
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact valid_join_cut hcond.1.1 hcond.1.2 hcond.2 (join ri.1 rj.1)
          · exact readCutsLoop_sound b mbits P_cl cls v join force excl cnt rj.2 p.1 p.2 hrec c hmem

def GhostState (n B0 : ℕ) (v : ℕ → ℤ) (S : ℤ) (pr nr rh tt : ℕ) : Prop :=
  ∃ p q : ℕ → ℕ,
    pr = packVec16 n p 0 ∧
    nr = packVec16 n q 0 ∧
    (∀ k < n, p k ≤ B0 + 2 * tt ∧ q k ≤ B0 + 2 * tt) ∧
    vecSumZ p q v n 0 - (rh : ℤ) ≤ S

lemma ghost_step {n B0 : ℕ} {v : ℕ → ℤ} {S : ℤ} {pr nr rh tt pv nv ra : ℕ} (mult : ℕ)
    (hg : GhostState n B0 v S pr nr rh tt)
    (hc : ValidSwarCut n v (SwarCut.mk pv nv ra)) :
    GhostState n B0 v S (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
      (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult) := by
  obtain ⟨p, q, hpr, hnr, hbnd, hsum⟩ := hg
  obtain ⟨pA, qA, hpv, hnv, hbA, hsumA⟩ := hc
  refine ⟨fun i => p i + mult * pA i, fun i => q i + mult * qA i, ?_, ?_, ?_, ?_⟩
  · change pr + mult * pv = _
    rw [hpr, hpv, packVec16_mul, packVec16_add]
  · change nr + mult * nv = _
    rw [hnr, hnv, packVec16_mul, packVec16_add]
  · intro k hk
    obtain ⟨hp, hq⟩ := hbnd k hk
    obtain ⟨hpA, hqA⟩ := hbA k hk
    change p k + mult * pA k ≤ B0 + 2 * (tt + mult) ∧ q k + mult * qA k ≤ B0 + 2 * (tt + mult)
    have hm1 : mult * pA k ≤ 2 * mult := by
      calc mult * pA k ≤ mult * 2 := Nat.mul_le_mul_left mult hpA
        _ = 2 * mult := by ring
    have hm2 : mult * qA k ≤ 2 * mult := by
      calc mult * qA k ≤ mult * 2 := Nat.mul_le_mul_left mult hqA
        _ = 2 * mult := by ring
    omega
  · change vecSumZ _ _ v n 0 - ((rh + mult * ra : ℕ) : ℤ) ≤ S
    rw [vecSumZ_linear]
    have hmul : (mult : ℤ) * (vecSumZ pA qA v n 0 - (ra : ℤ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg mult) (sub_nonpos.mpr hsumA)
    push_cast; linarith

lemma ghost_step1 {n B0 : ℕ} {v : ℕ → ℤ} {S : ℤ} {pr nr rh tt pv nv ra : ℕ}
    (hg : GhostState n B0 v S pr nr rh tt)
    (hc : ValidSwarCut n v (SwarCut.mk pv nv ra)) :
    GhostState n B0 v S (Nat.add pr pv) (Nat.add nr nv) (Nat.add rh ra) (Nat.add tt 1) := by
  have h := ghost_step 1 hg hc
  simpa using h

inductive WalkRes where
  | mk (pr nr rh tt : Nat) (st : B32)

def walkSparseSym : Nat → CutRope4 → Nat → Nat → Nat → Nat → Nat → Nat → List Nat → WalkRes
  | 0, _, pr, nr, rh, tt, buf, av, ws => WalkRes.mk pr nr rh tt (B32.mk buf av ws)
  | Nat.succ fuel, rope, pr, nr, rh, tt, buf, av, ws =>
    match Nat.blt av 30 with
    | true =>
      match ws with
      | w :: ws' =>
        walkSparseSym fuel rope pr nr rh tt (Nat.add buf (Nat.mul w (Nat.pow 2 av))) (Nat.add av 32) ws'
      | [] =>
        walkSparseSym fuel rope pr nr rh tt buf 32 []
    | false =>
      match Nat.beq (Nat.mod buf 2) 1 with
      | true =>
        match Nat.blt (Nat.mod buf 8) 4 with
        | true =>
          match Nat.beq (Nat.mod buf 8) 1 with
          | true =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4) rope with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 32) (Nat.sub av 5) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              walkSparseSym fuel r1 (Nat.add pr pv) (Nat.add nr nv) (Nat.add rh ra) (Nat.add tt 1)
                (Nat.div buf 32) (Nat.sub av 5) ws
          | false =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4) (ropeDrop4 (Nat.mod (Nat.div buf 32) 4) rope) with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 128) (Nat.sub av 7) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              walkSparseSym fuel r1 (Nat.add pr pv) (Nat.add nr nv) (Nat.add rh ra) (Nat.add tt 1)
                (Nat.div buf 128) (Nat.sub av 7) ws
        | false =>
          match Nat.beq (Nat.mod buf 8) 5 with
          | true =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4) rope with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 128) (Nat.sub av 7) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              let mult := Nat.add 2 (Nat.mod (Nat.div buf 32) 4)
              walkSparseSym fuel r1
                (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
                (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult)
                (Nat.div buf 128) (Nat.sub av 7) ws
          | false =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4) (ropeDrop4 (Nat.mod (Nat.div buf 32) 4) rope) with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 1024) (Nat.sub av 10) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              let mult := Nat.add 1 (Nat.mod (Nat.div buf 128) 8)
              walkSparseSym fuel r1
                (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
                (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult)
                (Nat.div buf 1024) (Nat.sub av 10) ws
      | false =>
        match Nat.blt (Nat.mod buf 8) 4 with
        | true =>
          match Nat.beq (Nat.mod buf 8) 0 with
          | true =>
            WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 8) (Nat.sub av 3) ws)
          | false =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
                  (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
                  (ropeDrop16 (Nat.mod (Nat.div buf 128) 4) rope)) with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 8192) (Nat.sub av 13) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              let mult := Nat.add 1 (Nat.mod (Nat.div buf 512) 16)
              walkSparseSym fuel r1
                (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
                (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult)
                (Nat.div buf 8192) (Nat.sub av 13) ws
        | false =>
          match Nat.beq (Nat.mod buf 8) 4 with
          | true =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
                  (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
                  (ropeDrop16 (Nat.mod (Nat.div buf 128) 4) rope)) with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 65536) (Nat.sub av 16) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              let mult := Nat.add 1 (Nat.mod (Nat.div buf 512) 128)
              walkSparseSym fuel r1
                (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
                (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult)
                (Nat.div buf 65536) (Nat.sub av 16) ws
          | false =>
            match ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
                  (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
                  (ropeDrop16 (Nat.mod (Nat.div buf 128) 4)
                  (ropeDrop64 (Nat.mod (Nat.div buf 512) 64) rope))) with
            | CutRope4.nil => WalkRes.mk pr nr rh tt (B32.mk (Nat.div buf 0x20000000) (Nat.sub av 29) ws)
            | CutRope4.cons (SwarCut.mk pv nv ra) r1 _ _ _ =>
              let mult := Nat.add 1 (Nat.mod (Nat.div buf 32768) 16384)
              walkSparseSym fuel r1
                (Nat.add pr (Nat.mul mult pv)) (Nat.add nr (Nat.mul mult nv))
                (Nat.add rh (Nat.mul mult ra)) (Nat.add tt mult)
                (Nat.div buf 0x20000000) (Nat.sub av 29) ws

def WalkResGhost (n B0 : ℕ) (v : ℕ → ℤ) (S : ℤ) : WalkRes → Prop
  | WalkRes.mk pr nr rh tt _ => GhostState n B0 v S pr nr rh tt

lemma walkSparseSym_sound (n B0 : ℕ) (v : ℕ → ℤ) (S : ℤ) :
    ∀ (fuel : ℕ) (rope : CutRope4) (pr nr rh tt buf av : ℕ) (ws : List ℕ),
      AllRope (ValidSwarCut n v) rope →
      GhostState n B0 v S pr nr rh tt →
      WalkResGhost n B0 v S (walkSparseSym fuel rope pr nr rh tt buf av ws)
  | 0, _, _, _, _, _, _, _, _, _, hg => hg
  | fuel + 1, rope, pr, nr, rh, tt, buf, av, ws, hr, hg => by
    dsimp only [walkSparseSym]
    cases Nat.blt av 30
    · cases Nat.beq (Nat.mod buf 2) 1
      · cases Nat.blt (Nat.mod buf 8) 4
        · cases Nat.beq (Nat.mod buf 8) 4
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
              (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
              (ropeDrop16 (Nat.mod (Nat.div buf 128) 4)
              (ropeDrop64 (Nat.mod (Nat.div buf 512) 64) rope)))
            have hrd : AllRope (ValidSwarCut n v) r' :=
              ropeDrop1_all _ (ropeDrop4_all _ (ropeDrop16_all _ (ropeDrop64_all _ hr)))
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step _ hg hrd.1)
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
              (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
              (ropeDrop16 (Nat.mod (Nat.div buf 128) 4) rope))
            have hrd : AllRope (ValidSwarCut n v) r' :=
              ropeDrop1_all _ (ropeDrop4_all _ (ropeDrop16_all _ hr))
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step _ hg hrd.1)
        · cases Nat.beq (Nat.mod buf 8) 0
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4)
              (ropeDrop4 (Nat.mod (Nat.div buf 32) 4)
              (ropeDrop16 (Nat.mod (Nat.div buf 128) 4) rope))
            have hrd : AllRope (ValidSwarCut n v) r' :=
              ropeDrop1_all _ (ropeDrop4_all _ (ropeDrop16_all _ hr))
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step _ hg hrd.1)
          · exact hg
      · cases Nat.blt (Nat.mod buf 8) 4
        · cases Nat.beq (Nat.mod buf 8) 5
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4) (ropeDrop4 (Nat.mod (Nat.div buf 32) 4) rope)
            have hrd : AllRope (ValidSwarCut n v) r' := ropeDrop1_all _ (ropeDrop4_all _ hr)
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step _ hg hrd.1)
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4) rope
            have hrd : AllRope (ValidSwarCut n v) r' := ropeDrop1_all _ hr
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step _ hg hrd.1)
        · cases Nat.beq (Nat.mod buf 8) 1
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4) (ropeDrop4 (Nat.mod (Nat.div buf 32) 4) rope)
            have hrd : AllRope (ValidSwarCut n v) r' := ropeDrop1_all _ (ropeDrop4_all _ hr)
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step1 hg hrd.1)
          · set r' := ropeDrop1 (Nat.mod (Nat.div buf 8) 4) rope
            have hrd : AllRope (ValidSwarCut n v) r' := ropeDrop1_all _ hr
            cases hr' : r' with
            | nil => exact hg
            | cons c r1 _ _ _ =>
              rw [hr'] at hrd; rcases c with ⟨pv, nv, ra⟩
              exact walkSparseSym_sound n B0 v S fuel r1 _ _ _ _ _ _ _ hrd.2.1 (ghost_step1 hg hrd.1)
    · cases ws with
      | nil => exact walkSparseSym_sound n B0 v S fuel rope pr nr rh tt buf 32 [] hr hg
      | cons w ws' => exact walkSparseSym_sound n B0 v S fuel rope pr nr rh tt _ _ ws' hr hg

def walkTdSym (walkFuel : Nat) (rope : CutRope4) (pr nr rh tt : Nat) (st0 : B32) : WalkRes :=
  match st0 with
  | B32.mk b1 a1 w1 => walkSparseSym walkFuel rope pr nr rh tt b1 a1 w1

def runPropSym32 (b pMaskBig : Nat) (swaps : List (Nat × Nat)) (ord : List Nat) :
    Nat → Nat → Nat → B32 → Option (Nat × Nat × Bool × B32)
  | 0, zm, om, st => some (zm, om, false, st)
  | Nat.succ cnt, zm, om, st0 =>
    match readBits32 1 st0 with
    | (b0, st1) =>
      match Nat.beq b0 0 with
      | true =>
        match readBits32 b st1 with
        | (px, st2) =>
          match readBits32 b st2 with
          | (py, st3) =>
            match (hasBit om px && (hasBit om py || hasBit pMaskBig py)) with
            | false => none
            | true =>
              let w := Nat.lor px py
              match hasBit zm w with
              | true => match Nat.beq cnt 0 with | true => some (zm, om, true, st3) | false => none
              | false => runPropSym32 b pMaskBig swaps ord cnt zm (setBit om w) st3
      | false =>
        match readBits32 2 st1 with
        | (sub, st2) =>
          match Nat.beq sub 0 with
          | true =>
            match readBits32 b st2 with
            | (px, st3) =>
              match readBits32 b st3 with
              | (py, st4) =>
                let w := Nat.lor px py
                match (hasBit zm w && (hasBit om px || hasBit pMaskBig px)) with
                | false => none
                | true =>
                  match hasBit om py with
                  | true => match Nat.beq cnt 0 with | true => some (zm, om, true, st4) | false => none
                  | false => runPropSym32 b pMaskBig swaps ord cnt (setBit zm py) om st4
          | false =>
            match readBits32 3 st2 with
            | (sIdx, st3) =>
              match readBits32 b st3 with
              | (u, st4) =>
                match listGet? swaps sIdx with
                | none => none
                | some ij =>
                  let us := swapBit ij.1 ij.2 u
                  match Nat.beq sub 1 with
                  | true =>
                    match (hasBit zm u && symStepPrefix zm om ij.1 ij.2 u ord) with
                    | false => none
                    | true =>
                      match hasBit om us with
                      | true => match Nat.beq cnt 0 with | true => some (zm, om, true, st4) | false => none
                      | false => runPropSym32 b pMaskBig swaps ord cnt (setBit zm us) om st4
                  | false =>
                    match Nat.beq sub 2 with
                    | false => none
                    | true =>
                      match (hasBit om us && symStepPrefix zm om ij.1 ij.2 u ord) with
                      | false => none
                      | true =>
                        match hasBit zm u with
                        | true => match Nat.beq cnt 0 with | true => some (zm, om, true, st4) | false => none
                        | false => runPropSym32 b pMaskBig swaps ord cnt zm (setBit om u) st4

lemma runPropSym32_sound (b : ℕ) (P_cl : List ℕ) (swaps : List (ℕ × ℕ)) (ord : List ℕ) (v : ℕ → ℤ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (force : ∀ m ∈ P_cl, ∀ i, v i ≤ v (i ||| m))
    (hSym : ∀ ij ∈ swaps,
      lexVal (fun u => decide (v (swapBit ij.1 ij.2 u) = 1)) ord ≤
        lexVal (fun u => decide (v u = 1)) ord) :
    ∀ (cnt zm om : ℕ) (st0 : B32) (zm' om' : ℕ) (gotConf : Bool) (st' : B32),
      (∀ x, zm.testBit x = true → v x = 0) →
      (∀ x, om.testBit x = true → v x = 1) →
      runPropSym32 b (listToMask P_cl) swaps ord cnt zm om st0 = some (zm', om', gotConf, st') →
      (gotConf = true → False) ∧
      (gotConf = false → (∀ x, zm'.testBit x = true → v x = 0) ∧ (∀ x, om'.testBit x = true → v x = 1))
  | 0, zm, om, _, zm', om', gotConf, _, hz, ho, hok => by
    simp only [runPropSym32, Option.some.injEq, Prod.mk.injEq] at hok
    rcases hok with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨by simp, fun _ => ⟨hz, ho⟩⟩
  | cnt + 1, zm, om, st0, zm', om', gotConf, st', hz, ho, hok => by
    dsimp only [runPropSym32] at hok
    have hpz : ∀ x, zm.testBit x = true → decide (v x = 1) = false := by
      intro x hx; simp [hz x hx]
    have hpo : ∀ x, om.testBit x = true → decide (v x = 1) = true := by
      intro x hx; simp [ho x hx]
    set r0 := readBits32 1 st0
    cases hb0 : Nat.beq r0.1 0
    · rw [hb0] at hok; dsimp only at hok
      set rsub := readBits32 2 r0.2
      cases hsub0 : Nat.beq rsub.1 0
      · rw [hsub0] at hok; dsimp only at hok
        set rs := readBits32 3 rsub.2
        set ru := readBits32 b rs.2
        cases hsw : listGet? swaps rs.1 with
        | none => rw [hsw] at hok; cases hok
        | some ij =>
          rw [hsw] at hok; dsimp only at hok
          have hij_mem := listGet?_mem swaps rs.1 ij hsw
          cases hsub1 : Nat.beq rsub.1 1
          · rw [hsub1] at hok; dsimp only at hok
            cases hsub2 : Nat.beq rsub.1 2
            · rw [hsub2] at hok; cases hok
            · rw [hsub2] at hok; dsimp only at hok
              cases hchk : (hasBit om (swapBit ij.1 ij.2 ru.1) && symStepPrefix zm om ij.1 ij.2 ru.1 ord)
              · rw [hchk] at hok; cases hok
              · rw [hchk] at hok; dsimp only at hok
                simp only [Bool.and_eq_true, hasBit_eq_testBit] at hchk
                have hvus : v (swapBit ij.1 ij.2 ru.1) = 1 := ho _ hchk.1
                have hvu : v ru.1 = 1 := by
                  rcases bit ru.1 with h0 | h1
                  · exfalso
                    have hlt := symStepPrefix_lt hpz hpo (by simp [h0]) (decide_eq_true hvus) ord hchk.2
                    have hle := hSym ij hij_mem
                    omega
                  · exact h1
                cases hcf : hasBit zm ru.1
                · rw [hcf] at hok
                  have ho' : ∀ x, (setBit om ru.1).testBit x = true → v x = 1 := by
                    intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
                    rcases hx with h | rfl; exact ho x h; exact hvu
                  exact runPropSym32_sound b P_cl swaps ord v bit join force hSym cnt zm (setBit om ru.1) ru.2
                    zm' om' gotConf st' hz ho' hok
                · have hvu0 := hz ru.1 (by rwa [← hasBit_eq_testBit])
                  exfalso; omega
          · rw [hsub1] at hok; dsimp only at hok
            cases hchk : (hasBit zm ru.1 && symStepPrefix zm om ij.1 ij.2 ru.1 ord)
            · rw [hchk] at hok; cases hok
            · rw [hchk] at hok; dsimp only at hok
              simp only [Bool.and_eq_true, hasBit_eq_testBit] at hchk
              have hvu : v ru.1 = 0 := hz ru.1 hchk.1
              have hvus : v (swapBit ij.1 ij.2 ru.1) = 0 := by
                rcases bit (swapBit ij.1 ij.2 ru.1) with h0 | h1
                · exact h0
                · exfalso
                  have hlt := symStepPrefix_lt hpz hpo (by simp [hvu]) (decide_eq_true h1) ord hchk.2
                  have hle := hSym ij hij_mem
                  omega
              cases hcf : hasBit om (swapBit ij.1 ij.2 ru.1)
              · rw [hcf] at hok
                have hz' : ∀ x, (setBit zm (swapBit ij.1 ij.2 ru.1)).testBit x = true → v x = 0 := by
                  intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
                  rcases hx with h | rfl; exact hz x h; exact hvus
                exact runPropSym32_sound b P_cl swaps ord v bit join force hSym cnt
                  (setBit zm (swapBit ij.1 ij.2 ru.1)) om ru.2 zm' om' gotConf st' hz' ho hok
              · have hvus1 := ho _ (by rwa [← hasBit_eq_testBit])
                exfalso; omega
      · rw [hsub0] at hok; dsimp only at hok
        set rpx := readBits32 b rsub.2
        set rpy := readBits32 b rpx.2
        set w := Nat.lor rpx.1 rpy.1
        cases hchk : (hasBit zm w && (hasBit om rpx.1 || hasBit (listToMask P_cl) rpx.1))
        · rw [hchk] at hok; cases hok
        · rw [hchk] at hok; dsimp only at hok
          simp only [Bool.and_eq_true, Bool.or_eq_true, hasBit_eq_testBit, listToMask_testBit] at hchk
          have hvw0 : v (rpx.1 ||| rpy.1) = 0 := hz w hchk.1
          have hvpy0 : v rpy.1 = 0 := by
            rcases hchk.2 with hox | hpxP
            · have hvx1 := ho rpx.1 hox
              have hj := join rpx.1 rpy.1
              rcases bit rpy.1 with h0 | h1 <;> omega
            · have hf := force rpx.1 hpxP rpy.1
              rw [Nat.lor_comm] at hf
              rcases bit rpy.1 with h0 | h1 <;> omega
          cases hcf : hasBit om rpy.1
          · rw [hcf] at hok
            have hz' : ∀ x, (setBit zm rpy.1).testBit x = true → v x = 0 := by
              intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
              rcases hx with h | rfl; exact hz x h; exact hvpy0
            exact runPropSym32_sound b P_cl swaps ord v bit join force hSym cnt (setBit zm rpy.1) om rpy.2
              zm' om' gotConf st' hz' ho hok
          · have hvpy1 := ho rpy.1 (by rwa [← hasBit_eq_testBit])
            exfalso; omega
    · rw [hb0] at hok; dsimp only at hok
      set rpx := readBits32 b r0.2
      set rpy := readBits32 b rpx.2
      cases hchk : (hasBit om rpx.1 && (hasBit om rpy.1 || hasBit (listToMask P_cl) rpy.1))
      · rw [hchk] at hok; cases hok
      · rw [hchk] at hok; dsimp only at hok
        simp only [Bool.and_eq_true, Bool.or_eq_true, hasBit_eq_testBit, listToMask_testBit] at hchk
        have hvx1 := ho rpx.1 hchk.1
        have hvw1 : v (rpx.1 ||| rpy.1) = 1 := by
          rcases hchk.2 with hoy | hpyP
          · have hvy1 := ho rpy.1 hoy
            have hj := join rpx.1 rpy.1
            rcases bit (rpx.1 ||| rpy.1) with h0 | h1 <;> omega
          · have hf := force rpy.1 hpyP rpx.1
            rcases bit (rpx.1 ||| rpy.1) with h0 | h1 <;> omega
        set w := Nat.lor rpx.1 rpy.1
        cases hcf : hasBit zm w
        · rw [hcf] at hok
          have ho' : ∀ x, (setBit om w).testBit x = true → v x = 1 := by
            intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
            rcases hx with h | rfl; exact ho x h; exact hvw1
          exact runPropSym32_sound b P_cl swaps ord v bit join force hSym cnt zm (setBit om w) rpy.2
            zm' om' gotConf st' hz ho' hok
        · have hvw0 := hz w (by rwa [← hasBit_eq_testBit])
          exfalso; change v (rpx.1 ||| rpy.1) = 0 at hvw0; omega

inductive ArmPrep where
  | fail (st : B32)
  | doneTrue (st : B32)
  | cont (zm1 om1 : Nat) (st : B32)

def prepArm (b pMaskBig : Nat) (swaps : List (Nat × Nat)) (ord : List Nat)
    (conflictAlready : Bool) (zmIn omIn : Nat) (st0 : B32) : ArmPrep :=
  match readBits32 2 st0 with
  | (hdr2, stH) =>
    let isConf := Nat.beq (Nat.mod hdr2 2) 1
    match Nat.beq (Nat.div hdr2 2) 0 with
    | true =>
      match conflictAlready with
      | true => match isConf with | true => ArmPrep.doneTrue stH | false => ArmPrep.fail stH
      | false => match isConf with | true => ArmPrep.fail stH | false => ArmPrep.cont zmIn omIn stH
    | false =>
      match readVint32 stH with
      | (nsM1, stC) =>
        match conflictAlready with
        | true => ArmPrep.fail stC
        | false =>
          match runPropSym32 b pMaskBig swaps ord (Nat.add nsM1 1) zmIn omIn stC with
          | none => ArmPrep.fail stC
          | some (zm1, om1, gotConf, stNext) =>
            match isConf with
            | true => match gotConf with | true => ArmPrep.doneTrue stNext | false => ArmPrep.fail stNext
            | false => match gotConf with | true => ArmPrep.doneTrue stNext | false => ArmPrep.cont zm1 om1 stNext

lemma prepArm_sound (b : ℕ) (P_cl : List ℕ) (swaps : List (ℕ × ℕ)) (ord : List ℕ) (v : ℕ → ℤ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (force : ∀ m ∈ P_cl, ∀ i, v i ≤ v (i ||| m))
    (hSym : ∀ ij ∈ swaps,
      lexVal (fun u => decide (v (swapBit ij.1 ij.2 u) = 1)) ord ≤
        lexVal (fun u => decide (v u = 1)) ord)
    (conflictAlready : Bool) (zmIn omIn : ℕ) (st0 : B32)
    (hno_cf : conflictAlready = false)
    (hz : ∀ x, zmIn.testBit x = true → v x = 0)
    (ho : ∀ x, omIn.testBit x = true → v x = 1) :
    match prepArm b (listToMask P_cl) swaps ord conflictAlready zmIn omIn st0 with
    | ArmPrep.fail _ => True
    | ArmPrep.doneTrue _ => False
    | ArmPrep.cont zm1 om1 _ =>
      (∀ x, zm1.testBit x = true → v x = 0) ∧ (∀ x, om1.testBit x = true → v x = 1) := by
  dsimp [prepArm]
  rw [hno_cf]
  set rh := readBits32 2 st0
  cases Nat.beq (Nat.div rh.1 2) 0
  · set rv := readVint32 rh.2
    cases hrun : runPropSym32 b (listToMask P_cl) swaps ord (Nat.add rv.1 1) zmIn omIn rv.2 with
    | none => trivial
    | some res =>
      rcases res with ⟨zm1, om1, gotConf, stNext⟩
      have hs := runPropSym32_sound b P_cl swaps ord v bit join force hSym
        (Nat.add rv.1 1) zmIn omIn rv.2 zm1 om1 gotConf stNext hz ho hrun
      cases gotConf
      · cases Nat.beq (Nat.mod rh.1 2) 1
        · exact hs.2 rfl
        · trivial
      · cases Nat.beq (Nat.mod rh.1 2) 1 <;> exact hs.1 rfl
  · cases Nat.beq (Nat.mod rh.1 2) 1
    · exact ⟨hz, ho⟩
    · trivial

def checkLeaf16 (sp : Sp16) (n2bBias maxAbsC scale tgtMag : Nat) (tgtNeg : Bool)
    (pr nr rh tt zm om : Nat) : Bool :=
  match Nat.blt (Nat.add (Nat.mul scale maxAbsC) (Nat.mul 2 tt)) W16 with
  | false => false
  | true =>
    let lbBiased := lbSwar16 sp zm om pr nr
    let lhs := Nat.add (Nat.add n2bBias rh) 1
    let rhsB := Nat.add lbBiased scale
    match tgtNeg with
    | false => Nat.ble (Nat.add lhs (Nat.mul scale tgtMag)) rhsB
    | true => Nat.ble lhs (Nat.add rhsB (Nat.mul scale tgtMag))

def targetOf (tgtMag : ℕ) (tgtNeg : Bool) : ℤ :=
  if tgtNeg then -(tgtMag : ℤ) else (tgtMag : ℤ)

lemma checkLeaf16_sound {b maxAbsC scale tgtMag : ℕ} {tgtNeg : Bool}
    {pr nr rh tt zm om : ℕ} {v : ℕ → ℤ} {S : ℤ}
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (_hsc : 0 < scale)
    (hg : GhostState (2 ^ b) (scale * maxAbsC) v ((scale : ℤ) * S) pr nr rh tt)
    (hz : ∀ x, zm.testBit x = true → v x = 0)
    (ho : ∀ x, om.testBit x = true → v x = 1)
    (hok : checkLeaf16 (buildSp16 b) (Nat.mul (Nat.pow 2 b) BIAS16) maxAbsC scale tgtMag tgtNeg pr nr rh tt zm om = true) :
    targetOf tgtMag tgtNeg ≤ S := by
  unfold checkLeaf16 at hok
  cases hfit : Nat.blt (Nat.add (Nat.mul scale maxAbsC) (Nat.mul 2 tt)) W16
  · rw [hfit] at hok; cases hok
  · rw [hfit] at hok; dsimp only at hok
    simp only [Nat.blt_eq, nat_add_eq, nat_mul_eq] at hfit
    obtain ⟨p, q, rfl, rfl, hbnd, hsum⟩ := hg
    have hp : ∀ k < 2 ^ b, p (0 + k) < W16 := fun k hk => by
      rw [Nat.zero_add]; have := (hbnd k hk).1; omega
    have hq : ∀ k < 2 ^ b, q (0 + k) < W16 := fun k hk => by
      rw [Nat.zero_add]; have := (hbnd k hk).2; omega
    have hlb := lbSwar16_sound p q v bit b 0 zm om
      (fun k _ htb => by simpa using hz k htb)
      (fun k _ htb => by simpa using ho k htb)
      hp hq
    set lbB := lbSwar16 (buildSp16 b) zm om (packVec16 (2 ^ b) p 0) (packVec16 (2 ^ b) q 0)
    have hineq : (scale : ℤ) * targetOf tgtMag tgtNeg - (scale : ℤ) + 1 ≤
        (lbB : ℤ) - ((2 ^ b : ℕ) : ℤ) * (BIAS16 : ℤ) - (rh : ℤ) := by
      cases tgtNeg
      · simp only [Nat.ble_eq, nat_add_eq, nat_mul_eq, nat_pow_eq] at hok
        dsimp [targetOf]
        have hokZ : (((2 ^ b * BIAS16 + rh + 1 + scale * tgtMag : ℕ) : ℤ)) ≤ (((lbB + scale : ℕ) : ℤ)) :=
          Nat.cast_le.mpr hok
        push_cast at hokZ; linarith
      · simp only [Nat.ble_eq, nat_add_eq, nat_mul_eq, nat_pow_eq] at hok
        dsimp [targetOf]
        have hokZ : (((2 ^ b * BIAS16 + rh + 1 : ℕ) : ℤ)) ≤ (((lbB + scale + scale * tgtMag : ℕ) : ℤ)) :=
          Nat.cast_le.mpr hok
        push_cast at hokZ; linarith
    by_contra! hlt
    have hle : S ≤ targetOf tgtMag tgtNeg - 1 := by omega
    have hmul := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg scale)
    linarith

def evalSym (b n2bBias maxAbsC pMaskBig walkFuel tgtMag : Nat) (tgtNeg : Bool) (sp : Sp16)
    (posBase negBase : Nat) (swaps : List (Nat × Nat)) (ord : List Nat) (rope : CutRope4) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → B32 → Bool × B32
  | 0, _, _, _, _, _, _, _, st => (false, st)
  | Nat.succ fuel, scale, pr, nr, rh, tt, zm, om, st0 =>
    match readBits32 2 st0 with
    | (op, st1) =>
      match Nat.beq op 0 with
      | true =>
        match Nat.beq scale 0 with
        | true => (false, st1)
        | false => (checkLeaf16 sp n2bBias maxAbsC scale tgtMag tgtNeg pr nr rh tt zm om, st1)
      | false =>
        match Nat.beq op 1 with
        | true =>
          match Nat.beq scale 0 with
          | true => (false, st1)
          | false =>
            match walkTdSym walkFuel rope pr nr rh tt st1 with
            | WalkRes.mk pr' nr' rh' tt' st2 =>
              evalSym b n2bBias maxAbsC pMaskBig walkFuel tgtMag tgtNeg sp posBase negBase swaps ord rope
                fuel scale pr' nr' rh' tt' zm om st2
        | false =>
          match Nat.beq op 2 with
          | true =>
            match readVint32 st1 with
            | (scM1, st2) =>
              let scNew := Nat.add scM1 1
              match walkTdSym walkFuel rope (Nat.mul scNew posBase) (Nat.mul scNew negBase) 0 0 st2 with
              | WalkRes.mk pr' nr' rh' tt' st3 =>
                evalSym b n2bBias maxAbsC pMaskBig walkFuel tgtMag tgtNeg sp posBase negBase swaps ord rope
                  fuel scNew pr' nr' rh' tt' zm om st3
          | false =>
            match readBits32 b st1 with
            | (u, st2) =>
              match (match prepArm b pMaskBig swaps ord (hasBit om u) (setBit zm u) om st2 with
                     | ArmPrep.fail stF => (false, stF)
                     | ArmPrep.doneTrue stT => (true, stT)
                     | ArmPrep.cont zmL omL stL =>
                       evalSym b n2bBias maxAbsC pMaskBig walkFuel tgtMag tgtNeg sp posBase negBase swaps ord rope
                         fuel scale pr nr rh tt zmL omL stL) with
              | (false, stAfter0) => (false, stAfter0)
              | (true, stAfter0) =>
                match prepArm b pMaskBig swaps ord (hasBit zm u) zm (setBit om u) stAfter0 with
                | ArmPrep.fail stF => (false, stF)
                | ArmPrep.doneTrue stT => (true, stT)
                | ArmPrep.cont zmR omR stR =>
                  evalSym b n2bBias maxAbsC pMaskBig walkFuel tgtMag tgtNeg sp posBase negBase swaps ord rope
                    fuel scale pr nr rh tt zmR omR stR

lemma evalSym_sound (b maxAbsC walkFuel tgtMag : ℕ) (tgtNeg : Bool)
    (posBase negBase : ℕ) (p0 q0 : ℕ → ℕ)
    (hpBase : posBase = packVec16 (2 ^ b) p0 0)
    (hqBase : negBase = packVec16 (2 ^ b) q0 0)
    (hbBase : ∀ k < 2 ^ b, p0 k ≤ maxAbsC ∧ q0 k ≤ maxAbsC)
    (P_cl : List ℕ) (swaps : List (ℕ × ℕ)) (ord : List ℕ) (rope : CutRope4)
    (v : ℕ → ℤ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (force : ∀ m ∈ P_cl, ∀ i, v i ≤ v (i ||| m))
    (hSym : ∀ ij ∈ swaps,
      lexVal (fun u => decide (v (swapBit ij.1 ij.2 u) = 1)) ord ≤
        lexVal (fun u => decide (v u = 1)) ord)
    (hrope : AllRope (ValidSwarCut (2 ^ b) v) rope) :
    ∀ (fuel scale pr nr rh tt zm om : ℕ) (st0 : B32),
      (0 < scale → GhostState (2 ^ b) (scale * maxAbsC) v ((scale : ℤ) * vecSumZ p0 q0 v (2 ^ b) 0) pr nr rh tt) →
      (∀ x, zm.testBit x = true → v x = 0) →
      (∀ x, om.testBit x = true → v x = 1) →
      (evalSym b (Nat.mul (Nat.pow 2 b) BIAS16) maxAbsC (listToMask P_cl) walkFuel tgtMag tgtNeg
        (buildSp16 b) posBase negBase swaps ord rope fuel scale pr nr rh tt zm om st0).1 = true →
      targetOf tgtMag tgtNeg ≤ vecSumZ p0 q0 v (2 ^ b) 0
  | 0, _, _, _, _, _, _, _, _, _, _, _, hok => by simp [evalSym] at hok
  | fuel + 1, scale, pr, nr, rh, tt, zm, om, st0, hInv, hz, ho, hok => by
    set S := vecSumZ p0 q0 v (2 ^ b) 0
    dsimp only [evalSym] at hok
    set r0 := readBits32 2 st0
    cases hop0 : Nat.beq r0.1 0
    · rw [hop0] at hok; dsimp only at hok
      cases hop1 : Nat.beq r0.1 1
      · rw [hop1] at hok; dsimp only at hok
        cases hop2 : Nat.beq r0.1 2
        ·
          rw [hop2] at hok; dsimp only at hok
          set ru := readBits32 b r0.2
          set leftRes : Bool × B32 :=
            match prepArm b (listToMask P_cl) swaps ord (hasBit om ru.1) (setBit zm ru.1) om ru.2 with
            | ArmPrep.fail stF => (false, stF)
            | ArmPrep.doneTrue stT => (true, stT)
            | ArmPrep.cont zmL omL stL =>
              evalSym b (Nat.mul (Nat.pow 2 b) BIAS16) maxAbsC (listToMask P_cl) walkFuel tgtMag tgtNeg
                (buildSp16 b) posBase negBase swaps ord rope fuel scale pr nr rh tt zmL omL stL
          change (match leftRes with
            | (false, s) => (false, s)
            | (true, stAfter0) =>
              match prepArm b (listToMask P_cl) swaps ord (hasBit zm ru.1) zm (setBit om ru.1) stAfter0 with
              | ArmPrep.fail stF => (false, stF)
              | ArmPrep.doneTrue stT => (true, stT)
              | ArmPrep.cont zmR omR stR =>
                evalSym b (Nat.mul (Nat.pow 2 b) BIAS16) maxAbsC (listToMask P_cl) walkFuel tgtMag tgtNeg
                  (buildSp16 b) posBase negBase swaps ord rope fuel scale pr nr rh tt zmR omR stR).1 = true at hok
          rcases hlr : leftRes with ⟨bL, stAfter0⟩
          rw [hlr] at hok
          cases bL
          · cases hok
          · dsimp only at hok
            rcases bit ru.1 with hu0 | hu1
            ·
              have hno_cf0 : hasBit om ru.1 = false := by
                rw [hasBit_eq_testBit]
                cases hom : om.testBit ru.1
                · rfl
                · have := ho ru.1 hom; omega
              have hz0 : ∀ x, (setBit zm ru.1).testBit x = true → v x = 0 := by
                intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
                rcases hx with h | rfl; exact hz x h; exact hu0
              have hp0 := prepArm_sound b P_cl swaps ord v bit join force hSym
                (hasBit om ru.1) (setBit zm ru.1) om ru.2 hno_cf0 hz0 ho
              dsimp only [leftRes] at hlr
              cases hpa0 : prepArm b (listToMask P_cl) swaps ord (hasBit om ru.1) (setBit zm ru.1) om ru.2 with
              | fail _ => rw [hpa0] at hlr; cases hlr
              | doneTrue _ => rw [hpa0] at hp0; exact hp0.elim
              | cont zmL omL stL =>
                rw [hpa0] at hp0 hlr
                have hokL : (evalSym b (Nat.mul (Nat.pow 2 b) BIAS16) maxAbsC (listToMask P_cl) walkFuel tgtMag tgtNeg
                    (buildSp16 b) posBase negBase swaps ord rope fuel scale pr nr rh tt zmL omL stL).1 = true :=
                  congrArg Prod.fst hlr
                exact evalSym_sound b maxAbsC walkFuel tgtMag tgtNeg posBase negBase p0 q0 hpBase hqBase hbBase
                  P_cl swaps ord rope v bit join force hSym hrope fuel scale pr nr rh tt zmL omL stL
                  hInv hp0.1 hp0.2 hokL
            ·
              have hno_cf1 : hasBit zm ru.1 = false := by
                rw [hasBit_eq_testBit]
                cases hzm : zm.testBit ru.1
                · rfl
                · have := hz ru.1 hzm; omega
              have ho1 : ∀ x, (setBit om ru.1).testBit x = true → v x = 1 := by
                intro x hx; rw [setBit_testBit, Bool.or_eq_true, decide_eq_true_eq] at hx
                rcases hx with h | rfl; exact ho x h; exact hu1
              have hp1 := prepArm_sound b P_cl swaps ord v bit join force hSym
                (hasBit zm ru.1) zm (setBit om ru.1) stAfter0 hno_cf1 hz ho1
              cases hpa1 : prepArm b (listToMask P_cl) swaps ord (hasBit zm ru.1) zm (setBit om ru.1) stAfter0 with
              | fail _ => rw [hpa1] at hok; cases hok
              | doneTrue _ => rw [hpa1] at hp1; exact hp1.elim
              | cont zmR omR stR =>
                rw [hpa1] at hp1 hok
                exact evalSym_sound b maxAbsC walkFuel tgtMag tgtNeg posBase negBase p0 q0 hpBase hqBase hbBase
                  P_cl swaps ord rope v bit join force hSym hrope fuel scale pr nr rh tt zmR omR stR
                  hInv hp1.1 hp1.2 hok
        ·
          rw [hop2] at hok; dsimp only at hok
          set rv := readVint32 r0.2
          set scNew := Nat.add rv.1 1
          have hgInit : GhostState (2 ^ b) (scNew * maxAbsC) v ((scNew : ℤ) * S)
              (Nat.mul scNew posBase) (Nat.mul scNew negBase) 0 0 := by
            refine ⟨fun k => scNew * p0 k, fun k => scNew * q0 k, ?_, ?_, ?_, ?_⟩
            · change scNew * posBase = _; rw [hpBase, packVec16_mul]
            · change scNew * negBase = _; rw [hqBase, packVec16_mul]
            · intro k hk
              obtain ⟨h1, h2⟩ := hbBase k hk
              simp only [mul_zero, add_zero]
              exact ⟨Nat.mul_le_mul_left scNew h1, Nat.mul_le_mul_left scNew h2⟩
            · rw [vecSumZ_scale]; simp [S]
          rcases hw : walkTdSym walkFuel rope (Nat.mul scNew posBase) (Nat.mul scNew negBase) 0 0 rv.2 with ⟨pr', nr', rh', tt', st3⟩
          rw [hw] at hok
          have hgw : WalkResGhost (2 ^ b) (scNew * maxAbsC) v ((scNew : ℤ) * S)
              (walkTdSym walkFuel rope (Nat.mul scNew posBase) (Nat.mul scNew negBase) 0 0 rv.2) := by
            rcases rv.2 with ⟨b1, a1, w1⟩
            exact walkSparseSym_sound (2 ^ b) (scNew * maxAbsC) v ((scNew : ℤ) * S)
              walkFuel rope _ _ 0 0 b1 a1 w1 hrope hgInit
          rw [hw] at hgw
          exact evalSym_sound b maxAbsC walkFuel tgtMag tgtNeg posBase negBase p0 q0 hpBase hqBase hbBase
            P_cl swaps ord rope v bit join force hSym hrope fuel scNew pr' nr' rh' tt' zm om st3
            (fun _ => hgw) hz ho hok
      ·
        rw [hop1] at hok; dsimp only at hok
        cases hsc0 : Nat.beq scale 0
        · rw [hsc0] at hok; dsimp only at hok
          have hscPos : 0 < scale := by simp at hsc0; omega
          have hgCur := hInv hscPos
          rcases hw : walkTdSym walkFuel rope pr nr rh tt r0.2 with ⟨pr', nr', rh', tt', st2⟩
          rw [hw] at hok
          have hgw : WalkResGhost (2 ^ b) (scale * maxAbsC) v ((scale : ℤ) * S)
              (walkTdSym walkFuel rope pr nr rh tt r0.2) := by
            rcases r0.2 with ⟨b1, a1, w1⟩
            exact walkSparseSym_sound (2 ^ b) (scale * maxAbsC) v ((scale : ℤ) * S)
              walkFuel rope pr nr rh tt b1 a1 w1 hrope hgCur
          rw [hw] at hgw
          exact evalSym_sound b maxAbsC walkFuel tgtMag tgtNeg posBase negBase p0 q0 hpBase hqBase hbBase
            P_cl swaps ord rope v bit join force hSym hrope fuel scale pr' nr' rh' tt' zm om st2
            (fun _ => hgw) hz ho hok
        · rw [hsc0] at hok; cases hok
    ·
      rw [hop0] at hok; dsimp only at hok
      cases hsc0 : Nat.beq scale 0
      · rw [hsc0] at hok; dsimp only at hok
        have hscPos : 0 < scale := by simp at hsc0; omega
        exact checkLeaf16_sound bit hscPos (hInv hscPos) hz ho hok
      · rw [hsc0] at hok; cases hok

def checkInitDisjoint : List Nat → Nat → Bool
  | [], _ => true
  | u :: us, zm => match hasBit zm u with | true => false | false => checkInitDisjoint us zm

lemma checkInitDisjoint_false {zm : ℕ} {v : ℕ → ℤ}
    (hz : ∀ x, zm.testBit x = true → v x = 0) :
    ∀ (oList : List ℕ), (∀ u ∈ oList, v u = 1) → checkInitDisjoint oList zm = false → False
  | [], _, h => by cases h
  | u :: us, hoL, h => by
    dsimp [checkInitDisjoint] at h
    cases hb : hasBit zm u
    · rw [hb] at h
      exact checkInitDisjoint_false hz us (fun x hx => hoL x (List.mem_cons_of_mem _ hx)) h
    · have h0 := hz u (by rwa [← hasBit_eq_testBit])
      have h1 := hoL u List.mem_cons_self
      omega

def checkTaskSym (b mbits pMaskBig : Nat) (sp : Sp16) (posBase negBase maxAbsC : Nat) (target : Int)
    (swaps : List (Nat × Nat)) (ord : List Nat)
    (pArr : Arr8 Nat) (clArr : Arr8 (List Nat))
    (zList oList : List Nat) (fuel : Nat) (cs : List Nat) : Bool :=
  let n2b := Nat.pow 2 b
  let zm0 := listToMask zList
  match checkInitDisjoint oList zm0 with
  | false => true
  | true =>
    let om0 := listToMask oList
    let st0 := B32.mk 0 0 (chunksToWords32 cs)
    match readBits32 1 st0 with
    | (initConf, st1) =>
      match readVint32 st1 with
      | (nInitSteps, st2) =>
        match runPropSym32 b pMaskBig swaps ord nInitSteps zm0 om0 st2 with
        | none => false
        | some (zm, om, gotConf, st3) =>
          match Nat.beq initConf 1 with
          | true => gotConf
          | false =>
            match gotConf with
            | true => true
            | false =>
              match readVint32 st3 with
              | (mCuts, st4) =>
                match readCutsLoop b mbits n2b pArr clArr mCuts st4 with
                | none => false
                | some (cuts, st5) =>
                  let rope := buildCutRope4 cuts
                  let walkFuel := Nat.add (Nat.mul 2 mCuts) 8
                  match target with
                  | Int.ofNat n =>
                    (evalSym b (Nat.mul n2b BIAS16) maxAbsC pMaskBig walkFuel n false sp posBase negBase swaps ord rope
                      fuel 0 0 0 0 0 zm om st5).1
                  | Int.negSucc n =>
                    (evalSym b (Nat.mul n2b BIAS16) maxAbsC pMaskBig walkFuel (Nat.succ n) true sp posBase negBase swaps ord rope
                      fuel 0 0 0 0 0 zm om st5).1

lemma checkTaskSym_sound (b mbits : ℕ) (posBase negBase maxAbsC : ℕ) (p0 q0 : ℕ → ℕ)
    (hpBase : posBase = packVec16 (2 ^ b) p0 0)
    (hqBase : negBase = packVec16 (2 ^ b) q0 0)
    (hbBase : ∀ k < 2 ^ b, p0 k ≤ maxAbsC ∧ q0 k ≤ maxAbsC)
    (target : ℤ) (P_cl : List ℕ) (cls : List (List ℕ))
    (swaps : List (ℕ × ℕ)) (ord : List ℕ)
    (zList oList : List ℕ) (fuel : ℕ) (cs : List ℕ) (v : ℕ → ℤ)
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ i j, v i + v j - v (i ||| j) ≤ 1)
    (force : ∀ m ∈ P_cl, ∀ i, v i ≤ v (i ||| m))
    (excl : ∀ cl ∈ cls, (cl.map v).sum ≤ (cl.length : ℤ) - 1)
    (hSym : ∀ ij ∈ swaps,
      lexVal (fun u => decide (v (swapBit ij.1 ij.2 u) = 1)) ord ≤
        lexVal (fun u => decide (v u = 1)) ord)
    (hzL : ∀ u ∈ zList, v u = 0)
    (hoL : ∀ u ∈ oList, v u = 1)
    (hok : checkTaskSym b mbits (listToMask P_cl) (buildSp16 b) posBase negBase maxAbsC target
      swaps ord (listToArr8 P_cl) (listToArr8 cls) zList oList fuel cs = true) :
    target ≤ vecSumZ p0 q0 v (2 ^ b) 0 := by
  dsimp only [checkTaskSym] at hok
  have hzm0 : ∀ x, (listToMask zList).testBit x = true → v x = 0 :=
    fun x hx => hzL x ((listToMask_testBit zList x).mp hx)
  have hom0 : ∀ x, (listToMask oList).testBit x = true → v x = 1 :=
    fun x hx => hoL x ((listToMask_testBit oList x).mp hx)
  cases hdisj : checkInitDisjoint oList (listToMask zList)
  · exact (checkInitDisjoint_false hzm0 oList hoL hdisj).elim
  · rw [hdisj] at hok; dsimp only at hok
    set st0 := B32.mk 0 0 (chunksToWords32 cs)
    set r1 := readBits32 1 st0
    set r2 := readVint32 r1.2
    cases hrun : runPropSym32 b (listToMask P_cl) swaps ord r2.1 (listToMask zList) (listToMask oList) r2.2 with
    | none => rw [hrun] at hok; cases hok
    | some res =>
      rcases res with ⟨zm, om, gotConf, st3⟩
      rw [hrun] at hok; dsimp only at hok
      have hs := runPropSym32_sound b P_cl swaps ord v bit join force hSym
        r2.1 (listToMask zList) (listToMask oList) r2.2 zm om gotConf st3 hzm0 hom0 hrun
      cases gotConf
      · cases hic : Nat.beq r1.1 1
        · rw [hic] at hok; dsimp only at hok
          obtain ⟨hzm, hom⟩ := hs.2 rfl
          set r3 := readVint32 st3
          cases hcuts : readCutsLoop b mbits (Nat.pow 2 b) (listToArr8 P_cl) (listToArr8 cls) r3.1 r3.2 with
          | none => rw [hcuts] at hok; cases hok
          | some cp =>
            rcases cp with ⟨cuts, st5⟩
            rw [hcuts] at hok; dsimp only at hok
            have hvc := readCutsLoop_sound b mbits P_cl cls v join force excl r3.1 r3.2 cuts st5 hcuts
            have hrope := buildCutRope4_all _ cuts hvc
            cases target with
            | ofNat n =>
              have hev := evalSym_sound b maxAbsC (Nat.add (Nat.mul 2 r3.1) 8) n false
                posBase negBase p0 q0 hpBase hqBase hbBase P_cl swaps ord (buildCutRope4 cuts) v
                bit join force hSym hrope fuel 0 0 0 0 0 zm om st5 (by intro h; omega) hzm hom hok
              simpa [targetOf] using hev
            | negSucc n =>
              have hev := evalSym_sound b maxAbsC (Nat.add (Nat.mul 2 r3.1) 8) (Nat.succ n) true
                posBase negBase p0 q0 hpBase hqBase hbBase P_cl swaps ord (buildCutRope4 cuts) v
                bit join force hSym hrope fuel 0 0 0 0 0 zm om st5 (by intro h; omega) hzm hom hok
              dsimp [targetOf] at hev
              have hneg : Int.negSucc n = -(((n + 1 : ℕ) : ℤ)) := rfl
              rw [hneg]; simpa using hev
        · rw [hic] at hok; cases hok
      · exact (hs.1 rfl).elim


def mergeKeyPairs : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, xs, ys => xs ++ ys
  | Nat.succ fuel, xs, ys =>
    match xs with
    | [] => ys
    | x :: xs' =>
      match ys with
      | [] => xs
      | y :: ys' =>
        match Nat.ble x.1 y.1 with
        | true => x :: mergeKeyPairs fuel xs' ys
        | false => y :: mergeKeyPairs fuel xs ys'

def buildOrdPairs (b : Nat) (w_in : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, base =>
    [(Nat.add (Nat.mul (popCountAux b base) 0x1000000)
        (Nat.add (Nat.mul (maskWeightRec w_in base) 256) base), base)]
  | Nat.succ d, base =>
    mergeKeyPairs (Nat.pow 2 (Nat.add d 1))
      (buildOrdPairs b w_in d base)
      (buildOrdPairs b w_in d (Nat.add base (Nat.pow 2 d)))

def symOrd (b : Nat) (w_in : List Nat) : List Nat :=
  (buildOrdPairs b w_in b 0).map Prod.snd

def mBitsForAux : Nat → Nat → Nat → Nat
  | 0, _, d => d
  | Nat.succ fuel, plen, d =>
    match Nat.ble plen (Nat.pow 2 d) with
    | true => d
    | false => mBitsForAux fuel plen (Nat.add d 1)

def mBitsFor (plen : Nat) : Nat :=
  mBitsForAux 8 plen 0

lemma testBit_one_shiftLeft (x y : ℕ) : ((1 <<< x).testBit y) = decide (x = y) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

lemma mapMaskAux_testBit : ∀ (sig : List ℕ) (m y : ℕ),
    (mapMaskAux sig m).testBit y = true ↔
      ∃ (j : Fin sig.length), m.testBit j.val = true ∧ sig.get j = y
  | [], m, y => by simp [mapMaskAux]
  | x :: xs, m, y => by
    simp only [mapMaskAux, Nat.testBit_lor, Bool.or_eq_true]
    rw [mapMaskAux_testBit xs (m >>> 1) y]
    constructor
    · rintro (h0 | ⟨j, hj1, hj2⟩)
      · by_cases hm0 : m.testBit 0 = true
        · rw [if_pos hm0, testBit_one_shiftLeft, decide_eq_true_eq] at h0
          exact ⟨⟨0, Nat.zero_lt_succ _⟩, hm0, h0⟩
        · simp [hm0] at h0
      · refine ⟨j.succ, ?_, hj2⟩
        rw [Nat.testBit_shiftRight] at hj1
        simpa [Nat.add_comm 1 j.val] using hj1
    · rintro ⟨j, hj1, hj2⟩
      cases j using Fin.cases with
      | zero =>
        left
        simp only [Fin.val_zero] at hj1
        simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero] at hj2
        rw [if_pos hj1, testBit_one_shiftLeft, decide_eq_true_eq]
        exact hj2
      | succ k =>
        right
        refine ⟨k, ?_, ?_⟩
        · rw [Nat.testBit_shiftRight]
          simpa [Nat.add_comm 1 k.val] using hj1
        · simpa using hj2

def sigEmb {bp n : ℕ} (sig : List ℕ) (hlen : sig.length = bp) (hnd : sig.Nodup)
    (hbound : ∀ x ∈ sig, x < n) : Fin bp ↪ Fin n where
  toFun j := ⟨sig.get (j.cast hlen.symm), hbound _ (List.get_mem sig _)⟩
  inj' a b hab := by
    have h1 : sig.get (a.cast hlen.symm) = sig.get (b.cast hlen.symm) := congrArg Fin.val hab
    have h2 := (List.nodup_iff_injective_get.mp hnd) h1
    exact Fin.ext (by simpa using congrArg Fin.val h2)

lemma decode_mapMask {bp n : ℕ} (sig : List ℕ) (hlen : sig.length = bp) (hnd : sig.Nodup)
    (hbound : ∀ x ∈ sig, x < n) (m : ℕ) :
    decode n (mapMaskAux sig m) = (decode bp m).map (sigEmb sig hlen hnd hbound) := by
  ext y
  simp only [decode, mem_filter, mem_univ, true_and, mem_map]
  rw [mapMaskAux_testBit]
  constructor
  · rintro ⟨j, hj1, hj2⟩
    refine ⟨j.cast hlen, hj1, Fin.ext ?_⟩
    simpa [sigEmb] using hj2
  · rintro ⟨j, hj1, rfl⟩
    exact ⟨j.cast hlen.symm, by simpa using hj1, by simp [sigEmb]⟩

def appendEmb {b k : ℕ} {V : Type} (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) : Fin (b + k) ↪ V where
  toFun i := if h : i.val < b then e1 ⟨i.val, h⟩ else e2 ⟨i.val - b, by omega⟩
  inj' i j hij := by
    dsimp only at hij
    by_cases hi : i.val < b <;> by_cases hj : j.val < b
    · rw [dif_pos hi, dif_pos hj] at hij
      exact Fin.ext (congrArg (fun z : Fin b => z.val) (e1.injective hij))
    · rw [dif_pos hi, dif_neg hj] at hij
      exact (hd _ _ hij).elim
    · rw [dif_neg hi, dif_pos hj] at hij
      exact (hd _ _ hij.symm).elim
    · rw [dif_neg hi, dif_neg hj] at hij
      have hval : i.val - b = j.val - b := congrArg (fun z : Fin k => z.val) (e2.injective hij)
      exact Fin.ext (by omega)

lemma appendEmb_lt {b k : ℕ} {V : Type} (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) (i : Fin (b + k)) (hi : i.val < b) :
    appendEmb e1 e2 hd i = e1 ⟨i.val, hi⟩ := by
  change (if h : i.val < b then e1 ⟨i.val, h⟩ else e2 ⟨i.val - b, _⟩) = _
  rw [dif_pos hi]

lemma appendEmb_ge {b k : ℕ} {V : Type} (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) (i : Fin (b + k)) (hi : ¬ i.val < b) :
    appendEmb e1 e2 hd i = e2 ⟨i.val - b, by omega⟩ := by
  change (if h : i.val < b then e1 ⟨i.val, h⟩ else e2 ⟨i.val - b, _⟩) = _
  rw [dif_neg hi]

lemma appendEmb_range {b k : ℕ} {V : Type} [DecidableEq V] (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) :
    univ.map (appendEmb e1 e2 hd) = univ.map e1 ∪ univ.map e2 := by
  ext x
  simp only [mem_map, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < b
    · exact Or.inl ⟨⟨i.val, hi⟩, (appendEmb_lt e1 e2 hd i hi).symm⟩
    · exact Or.inr ⟨⟨i.val - b, by omega⟩, (appendEmb_ge e1 e2 hd i hi).symm⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨⟨j.val, by omega⟩, appendEmb_lt e1 e2 hd ⟨j.val, by omega⟩ j.isLt⟩
    · have hnb : ¬ (b + j.val < b) := by omega
      refine ⟨⟨b + j.val, by omega⟩, ?_⟩
      rw [appendEmb_ge e1 e2 hd ⟨b + j.val, by omega⟩ hnb]
      congr 1; ext; dsimp; omega

lemma disj_emb {b k : ℕ} {A B : Finset (Fin 12)} (eA : Fin b ↪ Fin 12) (eB : Fin k ↪ Fin 12)
    (hA : univ.map eA = A) (hB : univ.map eB = B) (hd : Disjoint A B) :
    ∀ i j, eA i ≠ eB j := by
  intro i j heq
  have h1 : eA i ∈ A := hA ▸ mem_map.mpr ⟨i, mem_univ _, rfl⟩
  have h2 : eA i ∈ B := hB ▸ (heq ▸ mem_map.mpr ⟨j, mem_univ _, rfl⟩)
  exact disjoint_left.mp hd h1 h2

lemma decode_low_append {b k : ℕ} {V : Type} [DecidableEq V] (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) {m : ℕ} (hm : m < 2 ^ b) :
    (decode (b + k) m).map (appendEmb e1 e2 hd) = (decode b m).map e1 := by
  ext x
  simp only [decode, mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hbit, rfl⟩
    have hi : i.val < b := by
      by_contra! hge
      have h0 : m.testBit i.val = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) hge))
      rw [hbit] at h0; cases h0
    exact ⟨⟨i.val, hi⟩, hbit, (appendEmb_lt e1 e2 hd i hi).symm⟩
  · rintro ⟨j, hbit, rfl⟩
    exact ⟨⟨j.val, by omega⟩, hbit, appendEmb_lt e1 e2 hd ⟨j.val, by omega⟩ j.isLt⟩

lemma decode_high_append {b k : ℕ} {V : Type} [DecidableEq V] (e1 : Fin b ↪ V) (e2 : Fin k ↪ V)
    (hd : ∀ i j, e1 i ≠ e2 j) {u : ℕ} :
    (decode (b + k) (u ||| ((2 ^ k - 1) <<< b))).map (appendEmb e1 e2 hd) =
      (univ.map e2) ∪ (decode b u).map e1 := by
  ext x
  simp only [decode, mem_map, mem_filter, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨i, hbit, rfl⟩
    rw [Nat.testBit_lor, Bool.or_eq_true] at hbit
    by_cases hi : i.val < b
    · have hsh : (((2 ^ k - 1) <<< b).testBit i.val) = false := by
        rw [Nat.testBit_shiftLeft]; simp [not_le.mpr hi]
      have hbit' : u.testBit i.val = true := by
        rcases hbit with h1 | h2
        · exact h1
        · rw [hsh] at h2; cases h2
      right
      exact ⟨⟨i.val, hi⟩, hbit', (appendEmb_lt e1 e2 hd i hi).symm⟩
    · left
      exact ⟨⟨i.val - b, by omega⟩, (appendEmb_ge e1 e2 hd i hi).symm⟩
  · rintro (⟨j, rfl⟩ | ⟨j, hbit, rfl⟩)
    · have hnb : ¬ (b + j.val < b) := by omega
      refine ⟨⟨b + j.val, by omega⟩, ?_, ?_⟩
      · rw [Nat.testBit_lor, Bool.or_eq_true]; right
        rw [Nat.testBit_shiftLeft]; simp [Nat.testBit_two_pow_sub_one, j.isLt]
      · rw [appendEmb_ge e1 e2 hd ⟨b + j.val, by omega⟩ hnb]
        congr 1; ext; dsimp; omega
    · refine ⟨⟨j.val, by omega⟩, ?_, appendEmb_lt e1 e2 hd ⟨j.val, by omega⟩ j.isLt⟩
      rw [Nat.testBit_lor, Bool.or_eq_true]; exact Or.inl hbit

def checkClosureStep (known : List ℕ) (m : ℕ) : Bool :=
  listContainsNat known m || listAny (fun a => listAny (fun c => Nat.beq (Nat.lor a c) m) known) known

def checkClosure : List ℕ → List ℕ → Bool
  | _, [] => true
  | known, m :: rest => checkClosureStep known m && checkClosure (m :: known) rest

lemma decode_union (b x y : ℕ) : decode b (x ||| y) = decode b x ∪ decode b y :=
  FranklLocal.decode_union b x y

lemma closure_mem {b : ℕ} {F : Finset (Finset (Fin 12))} (closed : IsUnionClosed F)
    (e : Fin b ↪ Fin 12) :
    ∀ (known extra : List ℕ),
      (∀ m ∈ known, (decode b m).map e ∈ F) →
      checkClosure known extra = true →
      ∀ m ∈ extra ++ known, (decode b m).map e ∈ F
  | known, [], hknown, _ => by simpa using hknown
  | known, m :: rest, hknown, hok => by
    simp only [checkClosure, Bool.and_eq_true] at hok
    have hm : (decode b m).map e ∈ F := by
      have hcs := hok.1
      simp only [checkClosureStep, Bool.or_eq_true, listContainsNat_iff, listAny_iff,
        nat_beq_true, nat_lor_eq] at hcs
      rcases hcs with hin | ⟨a, ha, c, hc, rfl⟩
      · exact hknown m hin
      · rw [decode_union b a c, map_union]
        exact closed _ (hknown a ha) _ (hknown c hc)
    have hcons : ∀ x ∈ m :: known, (decode b x).map e ∈ F := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxk
      · exact hm
      · exact hknown x hxk
    have ih := closure_mem closed e (m :: known) rest hcons hok.2
    intro x hx
    rw [List.cons_append] at hx
    rcases List.mem_cons.mp hx with rfl | hxrest
    · exact hm
    · exact ih x (by
        rcases List.mem_append.mp hxrest with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_cons_of_mem m h2))

lemma list_sum_le_length (v : ℕ → ℤ) : ∀ (l : List ℕ), (∀ x ∈ l, v x ≤ 1) → (l.map v).sum ≤ (l.length : ℤ)
  | [], _ => by simp
  | x :: xs, h1 => by
    have hx1 : v x ≤ 1 := h1 x List.mem_cons_self
    have hxs := list_sum_le_length v xs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    omega

lemma list_sum_le_length_sub_one (v : ℕ → ℤ) : ∀ (l : List ℕ),
    (∀ x ∈ l, v x ≤ 1) → (∃ x ∈ l, v x ≤ 0) → (l.map v).sum ≤ (l.length : ℤ) - 1
  | [], _, ⟨_, h, _⟩ => by cases h
  | x :: xs, h1, ⟨y, hy, hy0⟩ => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rcases List.mem_cons.mp hy with rfl | hyxs
    · have hxs := list_sum_le_length v xs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
      omega
    · have hx1 : v x ≤ 1 := h1 x List.mem_cons_self
      have hih := list_sum_le_length_sub_one v xs (fun w hw => h1 w (List.mem_cons_of_mem _ hw)) ⟨y, hyxs, hy0⟩
      omega

def readExclLoop (b top n2b bk pMaskBig : Nat) (forbArr : Arr8 (Nat × List Nat)) :
    Nat → B32 → Option (List (List Nat))
  | 0, _ => some []
  | Nat.succ cnt, st0 =>
    match readBits32 9 st0 with
    | (hdr9, st2) =>
      let patIdx := Nat.mod hdr9 64
      let clLen := Nat.add (Nat.div hdr9 64) 1
      match getArr8? forbArr patIdx with
      | none => none
      | some (bp, pm) =>
        match readBits32 (Nat.mul 4 bp) st2 with
        | (sigBits, st3) =>
          match readNatList32 b clLen st3 with
          | (cl, st4) =>
            match checkExclPacked bp pm top n2b bk pMaskBig sigBits cl with
            | true =>
              match readExclLoop b top n2b bk pMaskBig forbArr cnt st4 with
              | none => none
              | some rest => some (cl :: rest)
            | false => none

def readExclChunks (b k : Nat) (P_cl : List Nat) (forbArr : Arr8 (Nat × List Nat)) (cs : List Nat) :
    Option (List (List Nat)) :=
  let n2b := Nat.pow 2 b
  let top := Nat.mul (Nat.sub (Nat.pow 2 k) 1) n2b
  let pMaskBig := listToMask P_cl
  match readVint32 (B32.mk 0 0 (chunksToWords32 cs)) with
  | (cnt, st1) => readExclLoop b top n2b (Nat.add b k) pMaskBig forbArr cnt st1

lemma excl_packed_sound {b k : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12)) (hKsub : K ⊆ univ \ (univ.map e)) (hKcard : K.card = k)
    (P_cl : List ℕ) (hP : ∀ m ∈ P_cl, (decode b m).map e ∈ F)
    (bp : ℕ) (pm : List ℕ) (hno : ¬ HasPattern bp pm F)
    (sigBits : ℕ) (cl : List ℕ)
    (hok : checkExclPacked bp pm (Nat.mul (Nat.sub (Nat.pow 2 k) 1) (Nat.pow 2 b))
      (Nat.pow 2 b) (Nat.add b k) (listToMask P_cl) sigBits cl = true) :
    let v (i : ℕ) : ℤ := if K ∪ (decode b i).map e ∈ F then 1 else 0
    (cl.map v).sum ≤ (cl.length : ℤ) - 1 := by
  classical
  intro v
  by_cases hall : ∀ u ∈ cl, K ∪ (decode b u).map e ∈ F
  · exfalso
    obtain ⟨eK, heK⟩ := FranklGlobal.coordinates K hKcard
    have hd : ∀ i j, e i ≠ eK j := by
      intro i j heq
      have h1 : e i ∈ univ.map e := mem_map.mpr ⟨i, mem_univ _, rfl⟩
      have h2 : e i ∈ K := heK ▸ (heq ▸ mem_map.mpr ⟨j, mem_univ _, rfl⟩)
      exact (mem_sdiff.mp (hKsub h2)).2 h1
    let eBK := appendEmb e eK hd
    simp only [checkExclPacked, Bool.and_eq_true, nat_mul_eq, nat_sub_eq, nat_pow_eq, nat_add_eq] at hok
    obtain ⟨⟨hsigV, _hclB⟩, hpmL⟩ := hok
    have hsigS := sigValid_sound bp (b + k) sigBits 0 hsigV
    let sig := unpackSig bp sigBits
    have hlen : sig.length = bp := unpackSig_length bp sigBits
    have hsigB : ∀ x ∈ sig, x < b + k := fun x hx => (hsigS.2 x hx).1
    let sEmb := sigEmb sig hlen hsigS.1 hsigB
    have hpm := (checkPmLoop_iff bp sigBits ((2 ^ k - 1) * 2 ^ b) (2 ^ b) (listToMask P_cl) cl pm).mp hpmL
    apply hno
    refine ⟨sEmb.trans eBK, ?_⟩
    intro m' hm'
    have hmap : ((decode bp m').map sEmb).map eBK = (decode (b + k) (mapMaskAux sig m')).map eBK := by
      rw [decode_mapMask sig hlen hsigS.1 hsigB m']
    rw [← map_map, hmap, ← mapMaskPacked_eq bp sigBits m']
    rcases hpm m' hm' with ⟨hlt, hinM⟩ | ⟨u, hucl, hMeq⟩
    · rw [decode_low_append e eK hd hlt]
      exact hP _ ((listToMask_testBit P_cl _).mp hinM)
    · have htop : (2 ^ k - 1) * 2 ^ b = (2 ^ k - 1) <<< b := (Nat.shiftLeft_eq (2 ^ k - 1) b).symm
      rw [hMeq, htop, decode_high_append e eK hd, heK]
      exact hall u hucl
  · simp only [not_forall] at hall
    obtain ⟨u0, hu0, hnot⟩ := hall
    apply list_sum_le_length_sub_one v cl
    · intro x _; dsimp [v]; split_ifs <;> omega
    · exact ⟨u0, hu0, by dsimp [v]; rw [if_neg hnot]⟩

lemma readExclLoop_sound {b k : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12)) (hKsub : K ⊆ univ \ (univ.map e)) (hKcard : K.card = k)
    (P_cl : List ℕ) (hP : ∀ m ∈ P_cl, (decode b m).map e ∈ F)
    (forbidden : List (ℕ × List ℕ)) (hno : ∀ p ∈ forbidden, ¬ HasPattern p.1 p.2 F) :
    ∀ (cnt : ℕ) (st0 : B32) (cls : List (List ℕ)),
      readExclLoop b (Nat.mul (Nat.sub (Nat.pow 2 k) 1) (Nat.pow 2 b)) (Nat.pow 2 b)
        (Nat.add b k) (listToMask P_cl) (listToArr8 forbidden) cnt st0 = some cls →
      let v (i : ℕ) : ℤ := if K ∪ (decode b i).map e ∈ F then 1 else 0
      ∀ cl ∈ cls, (cl.map v).sum ≤ (cl.length : ℤ) - 1
  | 0, _, cls, hok => by
    simp only [readExclLoop, Option.some.injEq] at hok
    subst hok; intro _ _ h; cases h
  | cnt + 1, st0, cls, hok => by
    dsimp only [readExclLoop] at hok
    set rh := readBits32 9 st0
    cases hget : getArr8? (listToArr8 forbidden) (Nat.mod rh.1 64) with
    | none => rw [hget] at hok; cases hok
    | some p =>
      rcases p with ⟨bp, pm⟩
      rw [hget] at hok; dsimp only at hok
      set rsb := readBits32 (Nat.mul 4 bp) rh.2
      set rcl := readNatList32 b (Nat.add (Nat.div rh.1 64) 1) rsb.2
      cases hchk : checkExclPacked bp pm (Nat.mul (Nat.sub (Nat.pow 2 k) 1) (Nat.pow 2 b))
          (Nat.pow 2 b) (Nat.add b k) (listToMask P_cl) rsb.1 rcl.1
      · rw [hchk] at hok; cases hok
      · rw [hchk] at hok; dsimp only at hok
        cases hrest : readExclLoop b (Nat.mul (Nat.sub (Nat.pow 2 k) 1) (Nat.pow 2 b)) (Nat.pow 2 b)
            (Nat.add b k) (listToMask P_cl) (listToArr8 forbidden) cnt rcl.2 with
        | none => rw [hrest] at hok; cases hok
        | some rest =>
          rw [hrest] at hok; simp only [Option.some.injEq] at hok
          subst hok
          intro v cl hcl
          rcases List.mem_cons.mp hcl with rfl | hmem
          · exact excl_packed_sound e K hKsub hKcard P_cl hP bp pm
              (hno (bp, pm) (getArr8?_mem forbidden _ (bp, pm) hget)) rsb.1 rcl.1 hchk
          · exact readExclLoop_sound e K hKsub hKcard P_cl hP forbidden hno cnt rcl.2 rest hrest cl hmem

lemma finRange_sum_getD (b : ℕ) (w_in : List ℕ) (hlen : w_in.length = b) :
    (∑ j : Fin b, w_in.getD j.val 0) = w_in.sum := by
  rw [Fin.sum_univ_def]
  subst hlen
  have hmap : (List.finRange w_in.length).map (fun j : Fin w_in.length => w_in.getD j.val 0) = w_in := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2; simp [List.getD_eq_getElem?_getD]
  rw [hmap]

lemma decode_two_pow_sub_one (b : ℕ) : decode b (2 ^ b - 1) = univ := by
  ext j; simp [decode, Nat.testBit_two_pow_sub_one]

lemma decode_zero (b : ℕ) : decode b 0 = ∅ := by
  ext j; simp [decode]

lemma range_decode_bijection {b : ℕ} (hb : b ≤ 7) :
    ((List.range (2 ^ b)).map (decode b)).toFinset = univ ∧
    ((List.range (2 ^ b)).map (decode b)).Nodup := by
  interval_cases b <;> decide +kernel

lemma slice_general {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (closed : IsUnionClosed F) (hK : K ⊆ univ \ (univ.map e)) :
    let B := (univ : Finset (Fin b)).map e
    let X (U : Finset (Fin b)) := K ∪ U.map e
    let D := (univ : Finset (Finset (Fin b))).filter (fun U => X U ∈ F)
    IsUnionClosed D ∧
    (∀ H : Finset (Fin b), H.map e ∈ F → ∀ U ∈ D, U ∪ H ∈ D) ∧
    (∀ U : Finset (Fin b), (X U).card = K.card + U.card) ∧
    (∀ g : Finset (Fin b) → ℤ,
      (∑ Y ∈ F.filter (fun Y => Y \ B = K), g (univ.filter (fun j : Fin b => e j ∈ Y))) =
        ∑ U ∈ D, g U) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  let X (U : Finset (Fin b)) := K ∪ U.map e
  let D := (univ : Finset (Finset (Fin b))).filter (fun U => X U ∈ F)
  have mem (U) : U ∈ D ↔ X U ∈ F := by simp [D]
  have inner (U : Finset (Fin b)) : U.map e ⊆ B := map_subset_map.mpr (subset_univ _)
  have dis : Disjoint K B := by
    apply disjoint_left.mpr
    intro i hi hb; exact (mem_sdiff.mp (hK hi)).2 hb
  have ins (U) : X U ∩ B = U.map e := by
    ext i; simp only [X, mem_inter, mem_union]; constructor
    · rintro ⟨h | h, hb⟩
      · exact (disjoint_left.mp dis h hb).elim
      · exact h
    · exact fun h => ⟨Or.inr h, inner U h⟩
  have out (U) : X U \ B = K := by
    ext i; simp only [X, mem_sdiff, mem_union]; constructor
    · rintro ⟨h | h, hb⟩
      · exact h
      · exact (hb (inner U h)).elim
    · exact fun h => ⟨Or.inl h, disjoint_left.mp dis h⟩
  have cardX (U) : (X U).card = K.card + U.card := by
    change (K ∪ U.map e).card = _
    rw [card_union_of_disjoint (dis.mono_right (inner U)), card_map]
  have inject : Function.Injective X := by
    intro U V eq
    exact Finset.map_injective e <| (ins U).symm.trans ((congrArg (· ∩ B) eq).trans (ins V))
  have pull_X (U : Finset (Fin b)) : univ.filter (fun j : Fin b => e j ∈ X U) = U := by
    ext j
    simp only [X, mem_filter, mem_univ, true_and, mem_union, mem_map]
    constructor
    · rintro (hk | ⟨j', hj'U, hj'eq⟩)
      · exact (disjoint_left.mp dis hk (mem_map.mpr ⟨j, mem_univ _, rfl⟩)).elim
      · exact e.injective hj'eq ▸ hj'U
    · intro hj; exact Or.inr ⟨j, hj, rfl⟩
  refine ⟨?_, ?_, cardX, ?_⟩
  · intro U hu V hv
    apply (mem _).mpr
    have := closed (X U) ((mem U).mp hu) (X V) ((mem V).mp hv)
    simpa [X, map_union, union_assoc, union_left_comm, union_comm] using this
  · intro H hH U hu
    apply (mem _).mpr
    have := closed _ ((mem _).mp hu) _ hH
    simpa [X, map_union, union_assoc] using this
  · intro g
    have eq : D.image X = F.filter (fun Y => Y \ B = K) := by
      ext Y; constructor
      · rintro hy
        obtain ⟨U, hu, rfl⟩ := mem_image.mp hy
        exact mem_filter.mpr ⟨(mem _).mp hu, out U⟩
      · intro hy
        obtain ⟨hf, base⟩ := mem_filter.mp hy
        let U := univ.filter (fun i : Fin b => e i ∈ Y)
        have val : X U = Y := by
          ext a; simp only [X, mem_union]
          by_cases h : a ∈ B
          · obtain ⟨i, _, rfl⟩ := mem_map.mp h
            have nk : e i ∉ K := fun hm => disjoint_left.mp dis hm (mem_map.mpr ⟨i, mem_univ _, rfl⟩)
            simp [U, nk]
          · have : a ∈ K ↔ a ∈ Y := by rw [← base]; simp [h]
            have hn : a ∉ U.map e := fun hu => h (inner U hu)
            simp [hn, this]
        exact mem_image.mpr ⟨U, (mem _).mpr (val ▸ hf), val⟩
    rw [← eq, sum_image (fun _ _ _ _ heq => inject heq)]
    apply sum_congr rfl; intro U _; rw [pull_X]

lemma inner_weight_sum {b : ℕ} (e : Fin b ↪ Fin 12) (wF : Fin b → ℕ) (Y : Finset (Fin 12)) :
    (∑ x ∈ Y, ∑ j : Fin b, if e j = x then wF j else 0) =
      ∑ j ∈ univ.filter (fun j : Fin b => e j ∈ Y), wF j := by
  rw [sum_comm, sum_filter]
  apply sum_congr rfl; intro j _; simp

lemma outer_weight_sum (B Y : Finset (Fin 12)) (d_out : ℕ) :
    (∑ x ∈ Y, if x ∈ B then 0 else d_out) = (Y \ B).card * d_out := by
  have hno : Y.filter (· ∉ B) = Y \ B := by ext; simp
  rw [sum_ite, sum_const_zero, zero_add, hno, sum_const, smul_eq_mul]

def checkFCItem (b : Nat) (pm extra w_in : List Nat) (T fuel : Nat) (cs : List Nat) : Bool :=
  let P_cl := extra ++ pm
  let n2b := Nat.pow 2 b
  let mbits := mBitsFor P_cl.length
  let pMaskBig := listToMask P_cl
  let sp := buildSp16 b
  let pArr := listToArr8 P_cl
  let clArr := listToArr8 ([] : List (List Nat))
  match buildInitVecs16 w_in 2 0 T n2b 0 with
  | (posBase, negBase, maxAbsC) =>
    checkTaskSym b mbits pMaskBig sp posBase negBase maxAbsC 0 [] [] pArr clArr [] [Nat.sub n2b 1] fuel cs

def checkFCFull (b : Nat) (pm extra w_in : List Nat) (T fuel : Nat) (cs : List Nat) : Bool :=
  Nat.ble b 7 &&
  Nat.beq w_in.length b &&
  Nat.blt 0 T &&
  Nat.beq w_in.sum T &&
  checkClosure pm extra &&
  listContainsNat (extra ++ pm) (Nat.sub (Nat.pow 2 b) 1) &&
  checkFCItem b pm extra w_in T fuel cs

lemma fc_full_sound {F : Finset (Finset (Fin 12))} (closed : IsUnionClosed F)
    {b : ℕ} {pm extra w_in : List ℕ} {T fuel : ℕ} {cs : List ℕ}
    (hok : checkFCFull b pm extra w_in T fuel cs = true)
    (hpat : HasPattern b pm F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  classical
  simp only [checkFCFull, Bool.and_eq_true, nat_ble_true, nat_beq_true, nat_blt_true,
    listContainsNat_iff, nat_sub_eq, nat_pow_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hb, hwlen⟩, hTpos⟩, hwsum⟩, hcl⟩, hfull_mem⟩, hcert⟩ := hok
  obtain ⟨e, he⟩ := hpat
  let B := (univ : Finset (Fin b)).map e
  let wF (j : Fin b) : ℕ := w_in.getD j.val 0
  let w (x : Fin 12) : ℕ := ∑ j : Fin b, if e j = x then wF j else 0
  have htot : (∑ i : Fin 12, w i) = T := by
    have h1 := inner_weight_sum e wF univ
    have h2 : univ.filter (fun j : Fin b => e j ∈ (univ : Finset (Fin 12))) = univ := by ext; simp
    rw [h2] at h1
    exact h1.trans ((finRange_sum_getD b w_in hwlen).trans hwsum)
  refine ⟨w, htot ▸ hTpos, ?_⟩
  rw [htot]
  suffices hnonneg : (0 : ℤ) ≤ ∑ Y ∈ F, (2 * (∑ i ∈ Y, (w i : ℤ)) - (T : ℤ)) by
    simp only [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hnonneg
    have hcast : (F.card : ℤ) * (T : ℤ) ≤ 2 * ∑ Y ∈ F, ∑ i ∈ Y, (w i : ℤ) := by linarith
    exact_mod_cast hcast
  apply FranklGlobal.reassemble F B _ 0
  intro K hK
  simp only [ite_self, sub_self]
  have hKsub := mem_powerset.mp hK
  obtain ⟨ucD, forceD, _, sumD⟩ := slice_general F e K closed hKsub
  let D := (univ : Finset (Finset (Fin b))).filter (fun U => K ∪ U.map e ∈ F)
  have hrew : (∑ Y ∈ F.filter (fun Y => Y \ B = K), (2 * (∑ i ∈ Y, (w i : ℤ)) - (T : ℤ))) =
      ∑ U ∈ D, (2 * (∑ j ∈ U, (wF j : ℤ)) - (T : ℤ)) := by
    calc
      _ = ∑ Y ∈ F.filter (fun Y => Y \ B = K),
            (2 * (∑ j ∈ univ.filter (fun j : Fin b => e j ∈ Y), (wF j : ℤ)) - (T : ℤ)) := by
        apply sum_congr rfl; intro Y _
        have hwY : ((∑ i ∈ Y, w i : ℕ) : ℤ) =
            ((∑ j ∈ univ.filter (fun j : Fin b => e j ∈ Y), wF j : ℕ) : ℤ) :=
          congrArg Nat.cast (inner_weight_sum e wF Y)
        push_cast at hwY; rw [hwY]
      _ = _ := sumD (fun U => 2 * (∑ j ∈ U, (wF j : ℤ)) - (T : ℤ))
  rw [hrew]
  by_cases hne : D.Nonempty
  · have hPcl := closure_mem closed e pm extra he hcl
    have hunivF : (univ : Finset (Fin b)).map e ∈ F := by
      rw [← decode_two_pow_sub_one b]; exact hPcl _ hfull_mem
    have htop : univ ∈ D := FranklGlobal.nonempty_full D hne (forceD univ hunivF)
    obtain ⟨hall, hnd⟩ := range_decode_bijection hb
    rw [FranklLocal.indexed_sum D (List.range (2 ^ b)) (decode b)
      (fun U => 2 * (∑ j ∈ U, (wF j : ℤ)) - (T : ℤ)) hall hnd]
    let v (i : ℕ) : ℤ := if decode b i ∈ D then 1 else 0
    have bit (i : ℕ) : v i = 0 ∨ v i = 1 := by dsimp [v]; split_ifs <;> simp
    have join := FranklLocal.indicator_join D ucD (decode b) (FranklLocal.decode_union b)
    have force (m : ℕ) (hm : m ∈ extra ++ pm) : ∀ i, v i ≤ v (i ||| m) :=
      FranklLocal.indicator_force D (decode b) (FranklLocal.decode_union b) (forceD (decode b m) (hPcl m hm))
    have hexcl : ∀ cl ∈ ([] : List (List ℕ)), (cl.map v).sum ≤ (cl.length : ℤ) - 1 := fun _ h => by cases h
    have hoL : ∀ u ∈ [2 ^ b - 1], v u = 1 := by
      intro u hu; rcases List.mem_cons.mp hu with rfl | h
      · dsimp [v]; rw [decode_two_pow_sub_one, if_pos htop]
      · cases h
    dsimp only [checkFCItem] at hcert
    have hiv := buildInitVecs16_spec w_in 2 0 T (2 ^ b) 0
    dsimp only at hiv
    rcases hbv : buildInitVecs16 w_in 2 0 T (Nat.pow 2 b) 0 with ⟨posBase, negBase, maxAbsC⟩
    rw [hbv] at hcert
    rw [nat_pow_eq] at hbv; rw [hbv] at hiv
    simp only [pow_zero, one_mul, zero_add, add_zero] at hiv
    let p0 (u : ℕ) : ℕ := 2 * maskWeightRec w_in u - T
    let q0 (u : ℕ) : ℕ := T - 2 * maskWeightRec w_in u
    have htask := checkTaskSym_sound b (mBitsFor (extra ++ pm).length) posBase negBase maxAbsC p0 q0
      hiv.1 hiv.2.1 hiv.2.2 0 (extra ++ pm) [] [] [] [] [2 ^ b - 1] fuel cs v
      bit join force hexcl (fun _ h => by cases h) (fun _ h => by cases h) hoL
      (by simpa [nat_sub_eq, nat_pow_eq] using hcert)
    have hvsum : vecSumZ p0 q0 v (2 ^ b) 0 =
        ((List.range (2 ^ b)).map (fun i => (2 * (∑ j ∈ decode b i, (wF j : ℤ)) - (T : ℤ)) * v i)).sum := by
      apply vecSumZ_eq_list_sum
      intro k _
      have hm := maskWeightRec_eq_sum w_in b k hwlen
      dsimp [p0, q0, wF]
      omega
    rw [hvsum] at htask
    exact htask
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]

def pop7 (m : ℕ) : ℕ :=
  (m &&& 1) + ((m >>> 1) &&& 1) + ((m >>> 2) &&& 1) + ((m >>> 3) &&& 1) +
  ((m >>> 4) &&& 1) + ((m >>> 5) &&& 1) + ((m >>> 6) &&& 1)

lemma pop7_eq_maskCard_check :
    ((List.range 128).all (fun m => pop7 m == maskCard 7 m)) = true := by decide +kernel

lemma pop7_eq_card {m : ℕ} (hm : m < 128) : pop7 m = (decode 7 m).card := by
  have h := pop7_eq_maskCard_check
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [h m hm, maskCard_eq_card]

lemma union_pair_bounds {V : Type} [DecidableEq V] {X Y : Finset V}
    (hne : X ≠ Y) (hX : X.card = 3) (hY : Y.card = 3) :
    4 ≤ (X ∪ Y).card ∧ (X ∪ Y).card ≤ 6 := by
  constructor
  · by_contra! hlt
    have heqX : X = X ∪ Y := eq_of_subset_of_card_le subset_union_left (by omega)
    have hYX : Y ⊆ X := heqX.symm ▸ subset_union_right
    exact hne (eq_of_subset_of_card_le hYX (by omega)).symm
  · have := card_union_le X Y; omega

lemma not_both_union_four {V : Type} [DecidableEq V] {X Y Z : Finset V}
    (hX : X.card = 3) (h6 : 6 ≤ (X ∪ Y ∪ Z).card)
    (hXY : (X ∪ Y).card = 4) (hXZ : (X ∪ Z).card = 4) : False := by
  have hu : (X ∪ Y) ∪ (X ∪ Z) = X ∪ Y ∪ Z := by ext a; simp; tauto
  have hi : X ⊆ (X ∪ Y) ∩ (X ∪ Z) := subset_inter subset_union_left subset_union_left
  have hic : 3 ≤ ((X ∪ Y) ∩ (X ∪ Z)).card := hX ▸ card_le_card hi
  have hadd := card_union_add_card_inter (X ∪ Y) (X ∪ Z)
  rw [hu, hXY, hXZ] at hadd; omega

lemma disjoint_distinct_union_six {V : Type} [DecidableEq V] {X Y Z : Finset V}
    (hYZ : Y ≠ Z) (hX : X.card = 3) (hY : Y.card = 3) (hZ : Z.card = 3)
    (hXY : (X ∪ Y).card = 6) (hXZ : (X ∪ Z).card = 6) : X ∪ Y ≠ X ∪ Z := by
  intro heq
  have hdXY : Disjoint X Y := by
    have hadd := card_union_add_card_inter X Y
    exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
  have hdXZ : Disjoint X Z := by
    have hadd := card_union_add_card_inter X Z
    exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
  have h1 : (X ∪ Y) \ X = Y := union_sdiff_cancel_left hdXY
  have h2 : (X ∪ Z) \ X = Z := union_sdiff_cancel_left hdXZ
  exact hYZ (h1.symm.trans ((congrArg (· \ X) heq).trans h2))

lemma lemma3_cards {F : Finset (Finset (Fin 12))} (closed : IsUnionClosed F)
    (U_out A B C : Finset (Fin 12))
    (hAF : A ∈ F) (hBF : B ∈ F) (hCF : C ∈ F)
    (hAU : A ⊆ U_out) (hBU : B ⊆ U_out) (hCU : C ⊆ U_out)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcA : A.card = 3) (hcB : B.card = 3) (hcC : C.card = 3)
    (h6 : 6 ≤ (A ∪ B ∪ C).card) :
    ((∃ K5 ⊆ U_out, K5.card = 5 ∧ K5 ∈ F) ∨
     (∃ K6 K6', K6 ⊆ U_out ∧ K6' ⊆ U_out ∧ K6 ≠ K6' ∧ K6.card = 6 ∧ K6'.card = 6 ∧ K6 ∈ F ∧ K6' ∈ F)) := by
  by_cases h5AB : (A ∪ B).card = 5
  · exact Or.inl ⟨A ∪ B, union_subset hAU hBU, h5AB, closed A hAF B hBF⟩
  by_cases h5AC : (A ∪ C).card = 5
  · exact Or.inl ⟨A ∪ C, union_subset hAU hCU, h5AC, closed A hAF C hCF⟩
  by_cases h5BC : (B ∪ C).card = 5
  · exact Or.inl ⟨B ∪ C, union_subset hBU hCU, h5BC, closed B hBF C hCF⟩
  have bAB := union_pair_bounds hAB hcA hcB
  have bAC := union_pair_bounds hAC hcA hcC
  have bBC := union_pair_bounds hBC hcB hcC
  have h6BAC : 6 ≤ (B ∪ A ∪ C).card := by
    have heq : B ∪ A ∪ C = A ∪ B ∪ C := by ext x; simp; tauto
    rwa [heq]
  have h6CAB : 6 ≤ (C ∪ A ∪ B).card := by
    have heq : C ∪ A ∪ B = A ∪ B ∪ C := by ext x; simp; tauto
    rwa [heq]
  have cAB : (A ∪ B).card = 4 ∨ (A ∪ B).card = 6 := by omega
  have cAC : (A ∪ C).card = 4 ∨ (A ∪ C).card = 6 := by omega
  have cBC : (B ∪ C).card = 4 ∨ (B ∪ C).card = 6 := by omega
  rcases cAB with h4AB | h6AB
  · rcases cAC with h4AC | h6AC
    · exact (not_both_union_four hcA h6 h4AB h4AC).elim
    · rcases cBC with h4BC | h6BC
      · have hBA4 : (B ∪ A).card = 4 := by rwa [union_comm]
        exact (not_both_union_four hcB h6BAC hBA4 h4BC).elim
      · right
        have hCA6 : (C ∪ A).card = 6 := by rwa [union_comm]
        have hCB6 : (C ∪ B).card = 6 := by rwa [union_comm]
        have hne : C ∪ A ≠ C ∪ B := disjoint_distinct_union_six hAB hcC hcA hcB hCA6 hCB6
        exact ⟨C ∪ A, C ∪ B, union_subset hCU hAU, union_subset hCU hBU, hne, hCA6, hCB6,
          closed C hCF A hAF, closed C hCF B hBF⟩
  · rcases cAC with h4AC | h6AC
    · rcases cBC with h4BC | h6BC
      · have hCA4 : (C ∪ A).card = 4 := by rwa [union_comm]
        have hCB4 : (C ∪ B).card = 4 := by rwa [union_comm]
        exact (not_both_union_four hcC h6CAB hCA4 hCB4).elim
      · right
        have hBA6 : (B ∪ A).card = 6 := by rwa [union_comm]
        have hne : B ∪ A ≠ B ∪ C := disjoint_distinct_union_six hAC hcB hcA hcC hBA6 h6BC
        exact ⟨B ∪ A, B ∪ C, union_subset hBU hAU, union_subset hBU hCU, hne, hBA6, h6BC,
          closed B hBF A hAF, closed B hBF C hCF⟩
    · right
      have hne : A ∪ B ≠ A ∪ C := disjoint_distinct_union_six hBC hcA hcB hcC h6AB h6AC
      exact ⟨A ∪ B, A ∪ C, union_subset hAU hBU, union_subset hAU hCU, hne, h6AB, h6AC,
        closed A hAF B hBF, closed A hAF C hCF⟩

def fcPatterns : List (ℕ × List ℕ) :=
  [(4, [11, 13, 14]), (5, [25, 26, 28]), (5, [21, 26, 28]), (5, [7, 26, 28]),
   (6, [7, 11, 52, 56]), (6, [7, 25, 42, 52]), (7, [81, 82, 100, 104]),
   (7, [49, 82, 100, 104]), (7, [25, 74, 100, 112]), (7, [25, 88, 98, 100]),
   (7, [13, 22, 104, 112]), (7, [13, 28, 98, 112]), (7, [56, 73, 82, 100]),
   (7, [13, 50, 84, 104])]

def validDirectEmb (bp n : ℕ) (pm targets sig : List ℕ) : Bool :=
  decide (sig.length = bp) &&
  nodupNat sig &&
  sig.all (· < n) &&
  pm.all (fun m' => targets.contains (mapMaskAux sig m'))

lemma validDirectEmb_sound {bp n : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin n ↪ Fin 12) (pm targets sig : List ℕ)
    (htgt : ∀ t ∈ targets, (decode n t).map e ∈ F)
    (hok : validDirectEmb bp n pm targets sig = true) :
    HasPattern bp pm F := by
  simp only [validDirectEmb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.contains_eq_mem] at hok
  obtain ⟨⟨⟨hlen, hndB⟩, hsigB⟩, hpm⟩ := hok
  have hnd := nodupNat_sound sig hndB
  let sEmb := sigEmb sig hlen hnd hsigB
  refine ⟨sEmb.trans e, ?_⟩
  intro m' hm'
  have hmap : ((decode bp m').map sEmb).map e = (decode n (mapMaskAux sig m')).map e := by
    rw [decode_mapMask sig hlen hnd hsigB m']
  rw [← map_map, hmap]
  exact htgt _ (hpm m' hm')

def fc5Wits : List (ℕ × ℕ × ℕ × ℕ × List ℕ) := [(7,11,13,0,[1,2,3,0]),(7,11,14,0,[0,2,3,1]),(7,11,19,1,[2,3,4,0,1]),(7,11,21,2,[3,4,1,2,0]),(7,11,22,2,[3,4,0,2,1]),(7,11,25,2,[2,4,1,3,0]),(7,11,26,2,[2,4,0,3,1]),(7,11,28,3,[4,2,3,0,1]),(7,13,14,0,[0,1,3,2]),(7,13,19,2,[3,4,2,1,0]),(7,13,21,1,[1,3,4,0,2]),(7,13,22,2,[3,4,0,1,2]),(7,13,25,2,[1,4,2,3,0]),(7,13,26,3,[4,1,3,0,2]),(7,13,28,2,[1,4,0,3,2]),(7,14,19,2,[3,4,2,0,1]),(7,14,21,2,[3,4,1,0,2]),(7,14,22,1,[0,3,4,1,2]),(7,14,25,3,[4,0,3,1,2]),(7,14,26,2,[0,4,2,3,1]),(7,14,28,2,[0,4,1,3,2]),(7,19,21,0,[1,2,4,0]),(7,19,22,0,[0,2,4,1]),(7,19,25,2,[2,3,1,4,0]),(7,19,26,2,[2,3,0,4,1]),(7,19,28,3,[3,2,4,0,1]),(7,21,22,0,[0,1,4,2]),(7,21,25,2,[1,3,2,4,0]),(7,21,26,3,[3,1,4,0,2]),(7,21,28,2,[1,3,0,4,2]),(7,22,25,3,[3,0,4,1,2]),(7,22,26,2,[0,3,2,4,1]),(7,22,28,2,[0,3,1,4,2]),(7,25,26,3,[2,0,1,3,4]),(7,25,28,3,[1,0,2,3,4]),(7,26,28,3,[0,1,2,3,4]),(11,13,14,0,[0,1,2,3]),(11,13,19,2,[2,4,3,1,0]),(11,13,21,2,[1,4,3,2,0]),(11,13,22,3,[4,1,2,0,3]),(11,13,25,1,[1,2,4,0,3]),(11,13,26,2,[2,4,0,1,3]),(11,13,28,2,[1,4,0,2,3]),(11,14,19,2,[2,4,3,0,1]),(11,14,21,3,[4,0,2,1,3]),(11,14,22,2,[0,4,3,2,1]),(11,14,25,2,[2,4,1,0,3]),(11,14,26,1,[0,2,4,1,3]),(11,14,28,2,[0,4,1,2,3]),(11,19,21,2,[3,2,1,4,0]),(11,19,22,2,[3,2,0,4,1]),(11,19,25,0,[1,3,4,0]),(11,19,26,0,[0,3,4,1]),(11,19,28,3,[2,3,4,0,1]),(11,21,22,3,[3,0,1,2,4]),(11,21,25,2,[1,2,3,4,0]),(11,21,26,3,[2,0,4,1,3]),(11,21,28,3,[1,0,3,2,4]),(11,22,25,3,[2,1,4,0,3]),(11,22,26,2,[0,2,3,4,1]),(11,22,28,3,[0,1,3,2,4]),(11,25,26,0,[0,1,4,3]),(11,25,28,2,[1,2,0,4,3]),(11,26,28,2,[0,2,1,4,3]),(13,14,19,3,[4,0,1,2,3]),(13,14,21,2,[1,4,3,0,2]),(13,14,22,2,[0,4,3,1,2]),(13,14,25,2,[1,4,2,0,3]),(13,14,26,2,[0,4,2,1,3]),(13,14,28,1,[0,1,4,2,3]),(13,19,21,2,[3,1,2,4,0]),(13,19,22,3,[3,0,2,1,4]),(13,19,25,2,[2,1,3,4,0]),(13,19,26,3,[2,0,3,1,4]),(13,19,28,3,[1,0,4,2,3]),(13,21,22,2,[3,1,0,4,2]),(13,21,25,0,[2,3,4,0]),(13,21,26,3,[1,3,4,0,2]),(13,21,28,0,[0,3,4,2]),(13,22,25,3,[1,2,4,0,3]),(13,22,26,3,[0,2,3,1,4]),(13,22,28,2,[0,1,3,4,2]),(13,25,26,2,[2,1,0,4,3]),(13,25,28,0,[0,2,4,3]),(13,26,28,2,[0,1,2,4,3]),(14,19,21,3,[3,1,2,0,4]),(14,19,22,2,[3,0,2,4,1]),(14,19,25,3,[2,1,3,0,4]),(14,19,26,2,[2,0,3,4,1]),(14,19,28,3,[0,1,4,2,3]),(14,21,22,2,[3,0,1,4,2]),(14,21,25,3,[1,2,3,0,4]),(14,21,26,3,[0,2,4,1,3]),(14,21,28,2,[1,0,3,4,2]),(14,22,25,3,[0,3,4,1,2]),(14,22,26,0,[2,3,4,1]),(14,22,28,0,[1,3,4,2]),(14,25,26,2,[2,0,1,4,3]),(14,25,28,2,[1,0,2,4,3]),(14,26,28,0,[1,2,4,3]),(19,21,22,0,[0,1,2,4]),(19,21,25,1,[1,2,3,0,4]),(19,21,26,2,[2,3,0,1,4]),(19,21,28,2,[1,3,0,2,4]),(19,22,25,2,[2,3,1,0,4]),(19,22,26,1,[0,2,3,1,4]),(19,22,28,2,[0,3,1,2,4]),(19,25,26,0,[0,1,3,4]),(19,25,28,2,[1,2,0,3,4]),(19,26,28,2,[0,2,1,3,4]),(21,22,25,2,[1,3,2,0,4]),(21,22,26,2,[0,3,2,1,4]),(21,22,28,1,[0,1,3,2,4]),(21,25,26,2,[2,1,0,3,4]),(21,25,28,0,[0,2,3,4]),(21,26,28,2,[0,1,2,3,4]),(22,25,26,2,[2,0,1,3,4]),(22,25,28,2,[1,0,2,3,4]),(22,26,28,0,[1,2,3,4]),(25,26,28,1,[0,1,2,3,4])]

def fc7Wits11 : List (ℕ × ℕ × ℕ × List ℕ) := [(49,81,6,[2,3,5,6,1,4,0]),(49,82,7,[5,6,2,3,4,0,1]),(49,84,8,[6,5,3,4,2,1,0]),(49,88,8,[6,5,2,4,3,1,0]),(49,97,6,[2,3,4,6,1,5,0]),(49,98,7,[4,6,2,3,5,0,1]),(49,100,8,[6,4,3,5,2,1,0]),(49,104,8,[6,4,2,5,3,1,0]),(49,112,9,[6,2,3,4,5,1,0]),(50,81,7,[5,6,2,3,4,1,0]),(50,82,6,[2,3,5,6,0,4,1]),(50,84,8,[6,5,3,4,2,0,1]),(50,88,8,[6,5,2,4,3,0,1]),(50,97,7,[4,6,2,3,5,1,0]),(50,98,6,[2,3,4,6,0,5,1]),(50,100,8,[6,4,3,5,2,0,1]),(50,104,8,[6,4,2,5,3,0,1]),(50,112,9,[6,2,3,4,5,0,1]),(52,56,4,[0,1,2,3,4,5]),(52,81,8,[5,6,3,4,2,1,0]),(52,82,8,[5,6,3,4,2,0,1]),(52,84,9,[3,5,6,0,1,4,2]),(52,88,10,[5,6,4,2,3,0,1]),(52,97,8,[4,6,3,5,2,1,0]),(52,98,8,[4,6,3,5,2,0,1]),(52,100,9,[3,4,6,0,1,5,2]),(52,104,10,[4,6,5,2,3,0,1]),(52,112,11,[3,6,0,1,2,4,5]),(56,81,8,[5,6,2,4,3,1,0]),(56,82,8,[5,6,2,4,3,0,1]),(56,84,10,[5,6,4,3,2,0,1]),(56,88,9,[2,5,6,0,1,4,3]),(56,97,8,[4,6,2,5,3,1,0]),(56,98,8,[4,6,2,5,3,0,1]),(56,100,10,[4,6,5,3,2,0,1]),(56,104,9,[2,4,6,0,1,5,3]),(56,112,11,[2,6,0,1,3,4,5]),(81,97,6,[2,3,4,5,1,6,0]),(81,98,7,[4,5,2,3,6,0,1]),(81,100,8,[5,4,3,6,2,1,0]),(81,104,8,[5,4,2,6,3,1,0]),(81,112,9,[5,2,3,4,6,1,0]),(82,97,7,[4,5,2,3,6,1,0]),(82,98,6,[2,3,4,5,0,6,1]),(82,100,8,[5,4,3,6,2,0,1]),(82,104,8,[5,4,2,6,3,0,1]),(82,112,9,[5,2,3,4,6,0,1]),(84,88,4,[0,1,2,3,4,6]),(84,97,8,[4,5,3,6,2,1,0]),(84,98,8,[4,5,3,6,2,0,1]),(84,100,9,[3,4,5,0,1,6,2]),(84,104,10,[4,5,6,2,3,0,1]),(84,112,11,[3,5,0,1,2,4,6]),(88,97,8,[4,5,2,6,3,1,0]),(88,98,8,[4,5,2,6,3,0,1]),(88,100,10,[4,5,6,3,2,0,1]),(88,104,9,[2,4,5,0,1,6,3]),(88,112,11,[2,5,0,1,3,4,6]),(97,112,9,[4,2,3,5,6,1,0]),(98,112,9,[4,2,3,5,6,0,1]),(100,104,4,[0,1,2,3,5,6]),(100,112,11,[3,4,0,1,2,5,6]),(104,112,11,[2,4,0,1,3,5,6])]

def fc7Wits25 : List (ℕ × ℕ × ℕ × List ℕ) := [(35,73,6,[2,5,4,6,1,3,0]),(35,74,7,[4,6,2,5,3,0,1]),(35,76,8,[6,4,5,3,2,1,0]),(35,81,6,[2,5,3,6,1,4,0]),(35,82,7,[3,6,2,5,4,0,1]),(35,84,8,[6,3,5,4,2,1,0]),(35,88,9,[6,2,5,3,4,1,0]),(35,104,8,[6,4,2,3,5,1,0]),(35,112,8,[6,3,2,4,5,1,0]),(37,73,6,[1,5,4,6,2,3,0]),(37,74,8,[6,4,5,3,1,2,0]),(37,76,7,[4,6,1,5,3,0,2]),(37,81,6,[1,5,3,6,2,4,0]),(37,82,8,[6,3,5,4,1,2,0]),(37,84,7,[3,6,1,5,4,0,2]),(37,88,9,[6,1,5,3,4,2,0]),(37,104,8,[6,4,1,3,5,2,0]),(37,112,8,[6,3,1,4,5,2,0]),(38,56,4,[1,2,0,5,3,4]),(38,73,9,[5,4,6,1,2,3,0]),(38,74,8,[4,6,5,3,0,2,1]),(38,76,8,[4,6,5,3,0,1,2]),(38,81,9,[5,3,6,1,2,4,0]),(38,82,8,[3,6,5,4,0,2,1]),(38,84,8,[3,6,5,4,0,1,2]),(38,88,11,[5,6,1,2,0,3,4]),(38,104,10,[4,6,3,0,5,1,2]),(38,112,10,[3,6,4,0,5,1,2]),(41,67,6,[2,6,4,5,1,3,0]),(41,69,6,[1,6,4,5,2,3,0]),(41,70,9,[6,4,5,1,2,3,0]),(41,74,7,[2,6,4,5,1,0,3]),(41,76,7,[1,6,4,5,2,0,3]),(41,82,8,[6,2,5,1,4,3,0]),(41,84,8,[6,1,5,2,4,3,0]),(41,98,8,[6,2,4,1,5,3,0]),(41,100,8,[6,1,4,2,5,3,0]),(42,52,5,[0,1,2,3,4,5]),(42,67,7,[4,5,2,6,3,0,1]),(42,69,8,[5,4,6,3,1,2,0]),(42,70,8,[4,5,6,3,0,2,1]),(42,73,7,[2,5,4,6,1,0,3]),(42,74,7,[2,4,5,6,0,1,3]),(42,76,12,[4,5,6,0,1,2,3]),(42,81,8,[5,2,6,1,3,4,0]),(42,82,12,[2,5,6,0,3,4,1]),(42,84,13,[5,6,1,3,2,4,0]),(42,88,8,[2,5,6,1,0,4,3]),(42,97,12,[2,4,6,1,3,5,0]),(42,98,8,[4,2,6,0,3,5,1]),(42,100,13,[4,6,0,3,2,5,1]),(42,104,8,[2,4,6,0,1,5,3]),(42,112,13,[2,6,0,1,4,5,3]),(44,50,5,[0,2,1,3,4,5]),(44,67,8,[5,4,6,3,2,1,0]),(44,69,7,[4,5,1,6,3,0,2]),(44,70,8,[4,5,6,3,0,1,2]),(44,73,7,[1,5,4,6,2,0,3]),(44,74,12,[4,5,6,0,2,1,3]),(44,76,7,[1,4,5,6,0,2,3]),(44,81,8,[5,1,6,2,3,4,0]),(44,82,13,[5,6,2,3,1,4,0]),(44,84,12,[1,5,6,0,3,4,2]),(44,88,8,[1,5,6,2,0,4,3]),(44,97,12,[1,4,6,2,3,5,0]),(44,98,13,[4,6,0,3,1,5,2]),(44,100,8,[4,1,6,0,3,5,2]),(44,104,8,[1,4,6,0,2,5,3]),(44,112,13,[1,6,0,2,4,5,3]),(49,67,6,[2,6,3,5,1,4,0]),(49,69,6,[1,6,3,5,2,4,0]),(49,70,9,[6,3,5,1,2,4,0]),(49,74,8,[6,2,5,1,3,4,0]),(49,76,8,[6,1,5,2,3,4,0]),(49,82,7,[2,6,3,5,1,0,4]),(49,84,7,[1,6,3,5,2,0,4]),(49,98,8,[6,2,3,1,5,4,0]),(49,100,8,[6,1,3,2,5,4,0]),(50,67,7,[3,5,2,6,4,0,1]),(50,69,8,[5,3,6,4,1,2,0]),(50,70,8,[3,5,6,4,0,2,1]),(50,73,8,[5,2,6,1,4,3,0]),(50,74,12,[2,5,6,0,4,3,1]),(50,76,13,[5,6,1,4,2,3,0]),(50,81,7,[2,5,3,6,1,0,4]),(50,82,7,[2,3,5,6,0,1,4]),(50,84,12,[3,5,6,0,1,2,4]),(50,88,8,[2,5,6,1,0,3,4]),(50,97,12,[2,3,6,1,4,5,0]),(50,98,8,[3,2,6,0,4,5,1]),(50,100,13,[3,6,0,4,2,5,1]),(50,104,13,[2,6,0,1,3,5,4]),(50,112,8,[2,3,6,0,1,5,4]),(52,67,8,[5,3,6,4,2,1,0]),(52,69,7,[3,5,1,6,4,0,2]),(52,70,8,[3,5,6,4,0,1,2]),(52,73,8,[5,1,6,2,4,3,0]),(52,74,13,[5,6,2,4,1,3,0]),(52,76,12,[1,5,6,0,4,3,2]),(52,81,7,[1,5,3,6,2,0,4]),(52,82,12,[3,5,6,0,2,1,4]),(52,84,7,[1,3,5,6,0,2,4]),(52,88,8,[1,5,6,2,0,3,4]),(52,97,12,[1,3,6,2,4,5,0]),(52,98,13,[3,6,0,4,1,5,2]),(52,100,8,[3,1,6,0,4,5,2]),(52,104,13,[1,6,0,2,3,5,4]),(52,112,8,[1,3,6,0,2,5,4]),(56,67,9,[5,2,6,3,4,1,0]),(56,69,9,[5,1,6,3,4,2,0]),(56,70,11,[5,6,3,4,0,1,2]),(56,74,8,[2,6,5,1,0,4,3]),(56,76,8,[1,6,5,2,0,4,3]),(56,82,8,[2,6,5,1,0,3,4]),(56,84,8,[1,6,5,2,0,3,4]),(56,98,10,[2,6,1,0,5,3,4]),(56,100,10,[1,6,2,0,5,3,4]),(67,104,8,[5,4,2,3,6,1,0]),(67,112,8,[5,3,2,4,6,1,0]),(69,104,8,[5,4,1,3,6,2,0]),(69,112,8,[5,3,1,4,6,2,0]),(70,88,4,[1,2,0,6,3,4]),(70,104,10,[4,5,3,0,6,1,2]),(70,112,10,[3,5,4,0,6,1,2]),(73,98,8,[5,2,4,1,6,3,0]),(73,100,8,[5,1,4,2,6,3,0]),(74,84,5,[0,1,2,3,4,6]),(74,97,12,[2,4,5,1,3,6,0]),(74,98,8,[4,2,5,0,3,6,1]),(74,100,13,[4,5,0,3,2,6,1]),(74,104,8,[2,4,5,0,1,6,3]),(74,112,13,[2,5,0,1,4,6,3]),(76,82,5,[0,2,1,3,4,6]),(76,97,12,[1,4,5,2,3,6,0]),(76,98,13,[4,5,0,3,1,6,2]),(76,100,8,[4,1,5,0,3,6,2]),(76,104,8,[1,4,5,0,2,6,3]),(76,112,13,[1,5,0,2,4,6,3]),(81,98,8,[5,2,3,1,6,4,0]),(81,100,8,[5,1,3,2,6,4,0]),(82,97,12,[2,3,5,1,4,6,0]),(82,98,8,[3,2,5,0,4,6,1]),(82,100,13,[3,5,0,4,2,6,1]),(82,104,13,[2,5,0,1,3,6,4]),(82,112,8,[2,3,5,0,1,6,4]),(84,97,12,[1,3,5,2,4,6,0]),(84,98,13,[3,5,0,4,1,6,2]),(84,100,8,[3,1,5,0,4,6,2]),(84,104,13,[1,5,0,2,3,6,4]),(84,112,8,[1,3,5,0,2,6,4]),(88,98,10,[2,5,1,0,6,3,4]),(88,100,10,[1,5,2,0,6,3,4]),(98,104,10,[2,4,0,1,3,5,6]),(98,112,10,[2,3,0,1,4,5,6]),(100,104,10,[1,4,0,2,3,5,6]),(100,112,10,[1,3,0,2,4,5,6])]

def checkFC5Table : Bool :=
  let ms := (List.range 32).filter (fun m => pop7 m == 3)
  ms.all (fun m1 => ms.all (fun m2 => ms.all (fun m3 =>
    !(decide (m1 < m2) && decide (m2 < m3)) ||
    fc5Wits.any (fun w =>
      w.1 == m1 && w.2.1 == m2 && w.2.2.1 == m3 &&
      match fcPatterns[w.2.2.2.1]? with
      | none => false
      | some (bp, pm) => validDirectEmb bp 5 pm [m1, m2, m3] w.2.2.2.2))))

lemma checkFC5Table_ok : checkFC5Table = true := by decide +kernel

def checkFC7Table (m2 : ℕ) (wits : List (ℕ × ℕ × ℕ × List ℕ)) : Bool :=
  let ms := (List.range 128).filter (fun m => pop7 m == 3 && m != 7 && m != m2 && decide (6 ≤ pop7 (7 ||| m2 ||| m)))
  ms.all (fun m3 => ms.all (fun m4 =>
    !(decide (m3 < m4) && decide (6 ≤ pop7 (7 ||| m3 ||| m4)) && decide (6 ≤ pop7 (m2 ||| m3 ||| m4))) ||
    wits.any (fun w =>
      w.1 == m3 && w.2.1 == m4 &&
      match fcPatterns[w.2.2.1]? with
      | none => false
      | some (bp, pm) => validDirectEmb bp 7 pm [7, m2, m3, m4] w.2.2.2)))

lemma checkFC7Table_11_ok : checkFC7Table 11 fc7Wits11 = true := by decide +kernel
lemma checkFC7Table_25_ok : checkFC7Table 25 fc7Wits25 = true := by decide +kernel

lemma mask_of_sub {b : ℕ} (hb : b ≤ 7) (e : Fin b ↪ Fin 12) {S : Finset (Fin 12)}
    (hS : S ⊆ univ.map e) :
    ∃ m < 2 ^ b, (decode b m).map e = S ∧ (decode b m).card = S.card := by
  classical
  let U := univ.filter (fun j : Fin b => e j ∈ S)
  have hUmap : U.map e = S := by
    ext x; simp only [U, mem_map, mem_filter, mem_univ, true_and]; constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hx; obtain ⟨j, _, rfl⟩ := mem_map.mp (hS hx); exact ⟨j, hx, rfl⟩
  obtain ⟨hall, _⟩ := range_decode_bijection hb
  have hmem : U ∈ ((List.range (2 ^ b)).map (decode b)).toFinset := hall.symm ▸ mem_univ U
  obtain ⟨m, hm, hdec⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
  refine ⟨m, List.mem_range.mp hm, ?_, ?_⟩
  · rw [hdec, hUmap]
  · rw [hdec, ← hUmap, card_map]

lemma sort_three_nat {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x y z : ℕ, x < y ∧ y < z ∧
      (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧ (z = a ∨ z = b ∨ z = c) := by
  by_cases h1 : a < b <;> by_cases h2 : b < c <;> by_cases h3 : a < c
  · exact ⟨a, b, c, h1, h2, Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · omega
  · exact ⟨a, c, b, h3, by omega, Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
  · exact ⟨c, a, b, by omega, h1, Or.inr (Or.inr rfl), Or.inl rfl, Or.inr (Or.inl rfl)⟩
  · exact ⟨b, a, c, by omega, h3, Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨b, c, a, h2, by omega, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl⟩
  · omega
  · exact ⟨c, b, a, by omega, by omega, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl), Or.inl rfl⟩

lemma pop7_of_mask5 {m : ℕ} (hm : m < 32) : pop7 m = (decode 5 m).card := by
  have hchk : ((List.range 32).all (fun x => pop7 x == maskCard 5 x)) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hchk
  rw [hchk m hm, maskCard_eq_card]

lemma no_three_3sets_in_5 {F : Finset (Finset (Fin 12))}
    (hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F)
    (A B C : Finset (Fin 12)) (hAF : A ∈ F) (hBF : B ∈ F) (hCF : C ∈ F)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hcA : A.card = 3) (hcB : B.card = 3) (hcC : C.card = 3) :
    6 ≤ (A ∪ B ∪ C).card := by
  classical
  by_contra! hlt
  have hle5 : (A ∪ B ∪ C).card ≤ 5 := by omega
  obtain ⟨E, hsubE, hcE⟩ := exists_superset_card_eq hle5 (by simp)
  obtain ⟨e5, he5⟩ := FranklGlobal.coordinates E hcE
  have hAE : A ⊆ univ.map e5 := he5 ▸ Subset.trans (subset_union_left.trans subset_union_left) hsubE
  have hBE : B ⊆ univ.map e5 := he5 ▸ Subset.trans (subset_union_right.trans subset_union_left) hsubE
  have hCE : C ⊆ univ.map e5 := he5 ▸ Subset.trans subset_union_right hsubE
  obtain ⟨a, ha, hda, hcda⟩ := mask_of_sub (by decide) e5 hAE
  obtain ⟨b, hb, hdb, hcdb⟩ := mask_of_sub (by decide) e5 hBE
  obtain ⟨c, hc, hdc, hcdc⟩ := mask_of_sub (by decide) e5 hCE
  have hab : a ≠ b := by rintro rfl; exact hAB (hda.symm.trans hdb)
  have hac : a ≠ c := by rintro rfl; exact hAC (hda.symm.trans hdc)
  have hbc : b ≠ c := by rintro rfl; exact hBC (hdb.symm.trans hdc)
  obtain ⟨m1, m2, m3, h12, h23, hm1c, hm2c, hm3c⟩ := sort_three_nat hab hac hbc
  have inF (m : ℕ) (hm : m = a ∨ m = b ∨ m = c) :
      m ∈ (List.range 32).filter (fun x => pop7 x == 3) ∧ (decode 5 m).map e5 ∈ F := by
    rcases hm with rfl | rfl | rfl
    · refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, hda ▸ hAF⟩
      rw [beq_iff_eq, pop7_of_mask5 (by omega), hcda, hcA]
    · refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, hdb ▸ hBF⟩
      rw [beq_iff_eq, pop7_of_mask5 (by omega), hcdb, hcB]
    · refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega), ?_⟩, hdc ▸ hCF⟩
      rw [beq_iff_eq, pop7_of_mask5 (by omega), hcdc, hcC]
  obtain ⟨hm1_in, hm1F⟩ := inF m1 hm1c
  obtain ⟨hm2_in, hm2F⟩ := inF m2 hm2c
  obtain ⟨hm3_in, hm3F⟩ := inF m3 hm3c
  have hok := checkFC5Table_ok
  simp only [checkFC5Table, List.all_eq_true] at hok
  have hinst := hok m1 hm1_in m2 hm2_in m3 hm3_in
  have hcond : (!(decide (m1 < m2) && decide (m2 < m3))) = false := by simp [h12, h23]
  rw [hcond, Bool.false_or] at hinst
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hinst
  obtain ⟨w, _, ⟨⟨⟨rfl, rfl⟩, rfl⟩, hmatch⟩⟩ := hinst
  cases hp : fcPatterns[w.2.2.2.1]? with
  | none => simp [hp] at hmatch
  | some p =>
    rcases p with ⟨bp, pm⟩
    simp only [hp] at hmatch
    have htgt : ∀ t ∈ [w.1, w.2.1, w.2.2.1], (decode 5 t).map e5 ∈ F := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm1F
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm2F
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hm3F
      cases ht
    exact hnoFC (bp, pm) (List.mem_of_getElem? hp) (validDirectEmb_sound e5 pm _ _ htgt hmatch)

lemma no_three_3sets_in_5_card {F : Finset (Finset (Fin 12))}
    (hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F)
    (E : Finset (Fin 12)) (hE : E.card ≤ 5) :
    (E.powerset.filter (fun K => K.card = 3 ∧ K ∈ F)).card ≤ 2 := by
  classical
  by_contra! hgt
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hgt
  obtain ⟨A, B, C, hAB, hAC, hBC, rfl⟩ := card_eq_three.mp hTcard
  have hA := mem_filter.mp (hTsub (mem_insert_self _ _))
  have hB := mem_filter.mp (hTsub (mem_insert_of_mem (mem_insert_self _ _)))
  have hC := mem_filter.mp (hTsub (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))))
  have h6 := no_three_3sets_in_5 hnoFC A B C hA.2.2 hB.2.2 hC.2.2 hAB hAC hBC hA.2.1 hB.2.1 hC.2.1
  have hsub : A ∪ B ∪ C ⊆ E := union_subset (union_subset (mem_powerset.mp hA.1) (mem_powerset.mp hB.1)) (mem_powerset.mp hC.1)
  have hle := (card_le_card hsub).trans hE
  omega

lemma embed_two_3sets_in_7 {E7 X1 X2 : Finset (Fin 12)}
    (hcE : E7.card = 7) (hX1E : X1 ⊆ E7) (hX2E : X2 ⊆ E7)
    (hc1 : X1.card = 3) (hc2 : X2.card = 3) (hne : X1 ≠ X2) (hpos : 1 ≤ (X1 ∩ X2).card) :
    (∃ e7 : Fin 7 ↪ Fin 12, univ.map e7 = E7 ∧ (decode 7 7).map e7 = X1 ∧ (decode 7 11).map e7 = X2) ∨
    (∃ e7 : Fin 7 ↪ Fin 12, univ.map e7 = E7 ∧ (decode 7 7).map e7 = X1 ∧ (decode 7 25).map e7 = X2) := by
  classical
  let C := X1 ∩ X2
  let D1 := X1 \ C
  let D2 := X2 \ C
  let R := E7 \ (X1 ∪ X2)
  have hCle2 : C.card ≤ 2 := by
    by_contra! hge3
    have heq1 : C = X1 := eq_of_subset_of_card_le inter_subset_left (by omega)
    have hsub : X1 ⊆ X2 := heq1 ▸ inter_subset_right
    exact hne (eq_of_subset_of_card_le hsub (by omega))
  have hdCD1 : Disjoint C D1 := disjoint_sdiff_self_right
  have huCD1 : C ∪ D1 = X1 := by ext x; simp only [C, D1, mem_union, mem_inter, mem_sdiff]; tauto
  have hdX1D2 : Disjoint X1 D2 := by
    apply disjoint_left.mpr; intro x hx1 hxD2
    obtain ⟨hx2, hnxC⟩ := mem_sdiff.mp hxD2
    exact hnxC (mem_inter.mpr ⟨hx1, hx2⟩)
  have huD2C : D2 ∪ C = X2 := by ext x; simp only [C, D2, mem_union, mem_inter, mem_sdiff]; tauto
  have huX1D2 : X1 ∪ D2 = X1 ∪ X2 := by
    ext x; simp only [D2, C, mem_union, mem_sdiff, mem_inter]; tauto
  have hdUR : Disjoint (X1 ∪ X2) R := disjoint_sdiff_self_right
  have huUR : (X1 ∪ X2) ∪ R = E7 := union_sdiff_of_subset (union_subset hX1E hX2E)
  have hcD1 : D1.card = 3 - C.card := by
    have := card_sdiff_of_subset (inter_subset_left (s₁ := X1) (s₂ := X2))
    dsimp [D1, C]; omega
  have hcD2 : D2.card = 3 - C.card := by
    have := card_sdiff_of_subset (inter_subset_right (s₁ := X1) (s₂ := X2))
    dsimp [D2, C]; omega
  have hcU : (X1 ∪ X2).card = 6 - C.card := by
    have := card_union_add_card_inter X1 X2
    change (X1 ∪ X2).card + C.card = _ at this; omega
  have hcR : R.card = 7 - (X1 ∪ X2).card := by
    have := card_sdiff_of_subset (union_subset hX1E hX2E)
    dsimp [R]; omega
  have hcases : C.card = 2 ∨ C.card = 1 := by change 1 ≤ C.card at hpos; omega
  have hd77 : decode 3 7 = univ := decode_two_pow_sub_one 3
  rcases hcases with hcC2 | hcC1
  · left
    obtain ⟨eC, heC⟩ := FranklGlobal.coordinates C hcC2
    obtain ⟨eD1, heD1⟩ := FranklGlobal.coordinates D1 (by omega : D1.card = 1)
    obtain ⟨eD2, heD2⟩ := FranklGlobal.coordinates D2 (by omega : D2.card = 1)
    obtain ⟨eR, heR⟩ := FranklGlobal.coordinates R (by omega : R.card = 3)
    let e3 := appendEmb eC eD1 (disj_emb eC eD1 heC heD1 hdCD1)
    have he3 : univ.map e3 = X1 := by rw [appendEmb_range, heC, heD1, huCD1]
    let e4 := appendEmb e3 eD2 (disj_emb e3 eD2 he3 heD2 hdX1D2)
    have he4 : univ.map e4 = X1 ∪ X2 := by rw [appendEmb_range, he3, heD2, huX1D2]
    let e7 := appendEmb e4 eR (disj_emb e4 eR he4 heR hdUR)
    have he7 : univ.map e7 = E7 := by rw [appendEmb_range, he4, heR, huUR]
    have h11 : (11 : ℕ) = 3 ||| ((2 ^ 1 - 1) <<< 3) := rfl
    have hd23 : decode 2 3 = univ := decode_two_pow_sub_one 2
    refine ⟨e7, he7, ?_, ?_⟩
    · rw [decode_low_append e4 eR _ (by decide : 7 < 2 ^ 4),
          decode_low_append e3 eD2 _ (by decide : 7 < 2 ^ 3), hd77, he3]
    · rw [decode_low_append e4 eR _ (by decide : 11 < 2 ^ 4), h11,
          decode_high_append e3 eD2 _, heD2,
          decode_low_append eC eD1 _ (by decide : 3 < 2 ^ 2), hd23, heC, huD2C]
  · right
    obtain ⟨eC, heC⟩ := FranklGlobal.coordinates C hcC1
    obtain ⟨eD1, heD1⟩ := FranklGlobal.coordinates D1 (by omega : D1.card = 2)
    obtain ⟨eD2, heD2⟩ := FranklGlobal.coordinates D2 (by omega : D2.card = 2)
    obtain ⟨eR, heR⟩ := FranklGlobal.coordinates R (by omega : R.card = 2)
    let e3 := appendEmb eC eD1 (disj_emb eC eD1 heC heD1 hdCD1)
    have he3 : univ.map e3 = X1 := by rw [appendEmb_range, heC, heD1, huCD1]
    let e5 := appendEmb e3 eD2 (disj_emb e3 eD2 he3 heD2 hdX1D2)
    have he5 : univ.map e5 = X1 ∪ X2 := by rw [appendEmb_range, he3, heD2, huX1D2]
    let e7 := appendEmb e5 eR (disj_emb e5 eR he5 heR hdUR)
    have he7 : univ.map e7 = E7 := by rw [appendEmb_range, he5, heR, huUR]
    have h25 : (25 : ℕ) = 1 ||| ((2 ^ 2 - 1) <<< 3) := rfl
    have hd11 : decode 1 1 = univ := decode_two_pow_sub_one 1
    refine ⟨e7, he7, ?_, ?_⟩
    · rw [decode_low_append e5 eR _ (by decide : 7 < 2 ^ 5),
          decode_low_append e3 eD2 _ (by decide : 7 < 2 ^ 3), hd77, he3]
    · rw [decode_low_append e5 eR _ (by decide : 25 < 2 ^ 5), h25,
          decode_high_append e3 eD2 _, heD2,
          decode_low_append eC eD1 _ (by decide : 1 < 2 ^ 1), hd11, heC, huD2C]

lemma apply_fc7_table {F : Finset (Finset (Fin 12))}
    (hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F)
    (e7 : Fin 7 ↪ Fin 12) (m2 : ℕ) (wits : List (ℕ × ℕ × ℕ × List ℕ))
    (htab : checkFC7Table m2 wits = true) (hm2_lt : m2 < 128)
    (X1 X2 X3 X4 : Finset (Fin 12))
    (h1F : X1 ∈ F) (h2F : X2 ∈ F) (h3F : X3 ∈ F) (h4F : X4 ∈ F)
    (hc1 : X1.card = 3) (hc2 : X2.card = 3) (hc3 : X3.card = 3) (hc4 : X4.card = 3)
    (hne12 : X1 ≠ X2) (hne13 : X1 ≠ X3) (hne14 : X1 ≠ X4)
    (hne23 : X2 ≠ X3) (hne24 : X2 ≠ X4) (hne34 : X3 ≠ X4)
    (hd1 : (decode 7 7).map e7 = X1) (hd2 : (decode 7 m2).map e7 = X2)
    (hX3 : X3 ⊆ univ.map e7) (hX4 : X4 ⊆ univ.map e7) : False := by
  classical
  obtain ⟨a, ha, hda, _⟩ := mask_of_sub (by decide) e7 hX3
  obtain ⟨b, hb, hdb, _⟩ := mask_of_sub (by decide) e7 hX4
  have ordered : ∃ m3 m4 : ℕ, m3 < m4 ∧ m3 < 128 ∧ m4 < 128 ∧
      ∃ Y3 Y4 : Finset (Fin 12), Y3 ∈ F ∧ Y4 ∈ F ∧ Y3.card = 3 ∧ Y4.card = 3 ∧
      X1 ≠ Y3 ∧ X1 ≠ Y4 ∧ X2 ≠ Y3 ∧ X2 ≠ Y4 ∧ Y3 ≠ Y4 ∧
      (decode 7 m3).map e7 = Y3 ∧ (decode 7 m4).map e7 = Y4 := by
    have hab : a ≠ b := by rintro rfl; exact hne34 (hda.symm.trans hdb)
    by_cases hlt : a < b
    · exact ⟨a, b, hlt, by omega, by omega, X3, X4, h3F, h4F, hc3, hc4,
        hne13, hne14, hne23, hne24, hne34, hda, hdb⟩
    · exact ⟨b, a, by omega, by omega, by omega, X4, X3, h4F, h3F, hc4, hc3,
        hne14, hne13, hne24, hne23, hne34.symm, hdb, hda⟩
  obtain ⟨m3, m4, hm34, hm3_lt, hm4_lt, Y3, Y4, hY3F, hY4F, hcY3, hcY4,
    h1Y3, h1Y4, h2Y3, h2Y4, hY34, hd3, hd4⟩ := ordered
  have union_pop (x y z : ℕ) (hx : x < 128) (hy : y < 128) (hz : z < 128)
      (Sx Sy Sz : Finset (Fin 12)) (hSxF : Sx ∈ F) (hSyF : Sy ∈ F) (hSzF : Sz ∈ F)
      (hxy : Sx ≠ Sy) (hxz : Sx ≠ Sz) (hyz : Sy ≠ Sz)
      (hcx : Sx.card = 3) (hcy : Sy.card = 3) (hcz : Sz.card = 3)
      (hdx : (decode 7 x).map e7 = Sx) (hdy : (decode 7 y).map e7 = Sy) (hdz : (decode 7 z).map e7 = Sz) :
      6 ≤ pop7 (x ||| y ||| z) := by
    have hx7 : x < 2 ^ 7 := hx; have hy7 : y < 2 ^ 7 := hy; have hz7 : z < 2 ^ 7 := hz
    have hxyz_lt : (x ||| y ||| z) < 128 := Nat.or_lt_two_pow (Nat.or_lt_two_pow hx7 hy7) hz7
    rw [pop7_eq_card hxyz_lt]
    have hdu : (decode 7 (x ||| y ||| z)).map e7 = Sx ∪ Sy ∪ Sz := by
      have h1 : decode 7 (x ||| y ||| z) = decode 7 (x ||| y) ∪ decode 7 z := FranklLocal.decode_union 7 (x ||| y) z
      have h2 : decode 7 (x ||| y) = decode 7 x ∪ decode 7 y := FranklLocal.decode_union 7 x y
      rw [h1, h2, map_union, map_union, hdx, hdy, hdz]
    have hcard : (decode 7 (x ||| y ||| z)).card = (Sx ∪ Sy ∪ Sz).card := by rw [← hdu, card_map]
    rw [hcard]
    exact no_three_3sets_in_5 hnoFC Sx Sy Sz hSxF hSyF hSzF hxy hxz hyz hcx hcy hcz
  have hp123 := union_pop 7 m2 m3 (by decide) hm2_lt hm3_lt X1 X2 Y3 h1F h2F hY3F hne12 h1Y3 h2Y3 hc1 hc2 hcY3 hd1 hd2 hd3
  have hp124 := union_pop 7 m2 m4 (by decide) hm2_lt hm4_lt X1 X2 Y4 h1F h2F hY4F hne12 h1Y4 h2Y4 hc1 hc2 hcY4 hd1 hd2 hd4
  have hp134 := union_pop 7 m3 m4 (by decide) hm3_lt hm4_lt X1 Y3 Y4 h1F hY3F hY4F h1Y3 h1Y4 hY34 hc1 hcY3 hcY4 hd1 hd3 hd4
  have hp234 := union_pop m2 m3 m4 hm2_lt hm3_lt hm4_lt X2 Y3 Y4 h2F hY3F hY4F h2Y3 h2Y4 hY34 hc2 hcY3 hcY4 hd2 hd3 hd4
  have hm3_ne7 : m3 ≠ 7 := by rintro rfl; exact h1Y3 (hd1.symm.trans hd3)
  have hm3_nem2 : m3 ≠ m2 := by rintro rfl; exact h2Y3 (hd2.symm.trans hd3)
  have hm4_ne7 : m4 ≠ 7 := by rintro rfl; exact h1Y4 (hd1.symm.trans hd4)
  have hm4_nem2 : m4 ≠ m2 := by rintro rfl; exact h2Y4 (hd2.symm.trans hd4)
  have hm3_pop : pop7 m3 = 3 := by rw [pop7_eq_card hm3_lt, ← card_map e7, hd3, hcY3]
  have hm4_pop : pop7 m4 = 3 := by rw [pop7_eq_card hm4_lt, ← card_map e7, hd4, hcY4]
  have hm3_in : m3 ∈ (List.range 128).filter (fun m => pop7 m == 3 && m != 7 && m != m2 && decide (6 ≤ pop7 (7 ||| m2 ||| m))) := by
    simp [hm3_lt, hm3_pop, hm3_ne7, hm3_nem2, hp123]
  have hm4_in : m4 ∈ (List.range 128).filter (fun m => pop7 m == 3 && m != 7 && m != m2 && decide (6 ≤ pop7 (7 ||| m2 ||| m))) := by
    simp [hm4_lt, hm4_pop, hm4_ne7, hm4_nem2, hp124]
  simp only [checkFC7Table, List.all_eq_true] at htab
  have hinst := htab m3 hm3_in m4 hm4_in
  have hcond : (!(decide (m3 < m4) && decide (6 ≤ pop7 (7 ||| m3 ||| m4)) && decide (6 ≤ pop7 (m2 ||| m3 ||| m4)))) = false := by
    simp [hm34, hp134, hp234]
  rw [hcond, Bool.false_or] at hinst
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hinst
  obtain ⟨w, _, ⟨⟨rfl, rfl⟩, hmatch⟩⟩ := hinst
  cases hp : fcPatterns[w.2.2.1]? with
  | none => simp [hp] at hmatch
  | some p =>
    rcases p with ⟨bp, pm⟩
    simp only [hp] at hmatch
    have htgt : ∀ t ∈ [7, m2, w.1, w.2.1], (decode 7 t).map e7 ∈ F := by
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hd1 ▸ h1F
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hd2 ▸ h2F
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hd3 ▸ hY3F
      rcases List.mem_cons.mp ht with rfl | ht
      · exact hd4 ▸ hY4F
      cases ht
    exact hnoFC (bp, pm) (List.mem_of_getElem? hp) (validDirectEmb_sound e7 pm _ _ htgt hmatch)

lemma no_four_3sets_in_7 {F : Finset (Finset (Fin 12))}
    (hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F)
    (E : Finset (Fin 12)) (hE : E.card ≤ 7) :
    (E.powerset.filter (fun K => K.card = 3 ∧ K ∈ F)).card ≤ 3 := by
  classical
  by_contra! hgt
  obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq hgt
  obtain ⟨g, hg⟩ := FranklGlobal.coordinates T hTcard
  obtain ⟨E7, hEE7, hcE7⟩ := exists_superset_card_eq hE (by simp)
  have hgT (r : Fin 4) : g r ∈ T := hg ▸ mem_map.mpr ⟨r, mem_univ _, rfl⟩
  have hgSub (r : Fin 4) : g r ⊆ E7 := (mem_powerset.mp (mem_filter.mp (hTsub (hgT r))).1).trans hEE7
  have hgCard (r : Fin 4) : (g r).card = 3 := (mem_filter.mp (hTsub (hgT r))).2.1
  have hgF (r : Fin 4) : g r ∈ F := (mem_filter.mp (hTsub (hgT r))).2.2
  have hgNe {r s : Fin 4} (hrs : r ≠ s) : g r ≠ g s := fun h => hrs (g.injective h)
  have hsome : 1 ≤ (g 0 ∩ g 1).card ∨ 1 ≤ (g 0 ∩ g 2).card ∨ 1 ≤ (g 1 ∩ g 2).card := by
    by_contra! h0
    have hd01 : Disjoint (g 0) (g 1) := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
    have hd02 : Disjoint (g 0) (g 2) := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
    have hd12 : Disjoint (g 1) (g 2) := disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
    have hc01 : (g 0 ∪ g 1).card = 6 := by rw [card_union_of_disjoint hd01, hgCard 0, hgCard 1]
    have hd012 : Disjoint (g 0 ∪ g 1) (g 2) := disjoint_union_left.mpr ⟨hd02, hd12⟩
    have hc012 : (g 0 ∪ g 1 ∪ g 2).card = 9 := by rw [card_union_of_disjoint hd012, hc01, hgCard 2]
    have hsub7 : g 0 ∪ g 1 ∪ g 2 ⊆ E7 := union_subset (union_subset (hgSub 0) (hgSub 1)) (hgSub 2)
    have hle7 := card_le_card hsub7
    omega
  have finish (X1 X2 X3 X4 : Finset (Fin 12))
      (h1E : X1 ⊆ E7) (h2E : X2 ⊆ E7) (h3E : X3 ⊆ E7) (h4E : X4 ⊆ E7)
      (h1F : X1 ∈ F) (h2F : X2 ∈ F) (h3F : X3 ∈ F) (h4F : X4 ∈ F)
      (hc1 : X1.card = 3) (hc2 : X2.card = 3) (hc3 : X3.card = 3) (hc4 : X4.card = 3)
      (hne12 : X1 ≠ X2) (hne13 : X1 ≠ X3) (hne14 : X1 ≠ X4)
      (hne23 : X2 ≠ X3) (hne24 : X2 ≠ X4) (hne34 : X3 ≠ X4)
      (hpos : 1 ≤ (X1 ∩ X2).card) : False := by
    rcases embed_two_3sets_in_7 hcE7 h1E h2E hc1 hc2 hne12 hpos with
      ⟨e7, he7, hd1, hd2⟩ | ⟨e7, he7, hd1, hd2⟩
    · exact apply_fc7_table hnoFC e7 11 fc7Wits11 checkFC7Table_11_ok (by decide)
        X1 X2 X3 X4 h1F h2F h3F h4F hc1 hc2 hc3 hc4
        hne12 hne13 hne14 hne23 hne24 hne34 hd1 hd2 (he7.symm ▸ h3E) (he7.symm ▸ h4E)
    · exact apply_fc7_table hnoFC e7 25 fc7Wits25 checkFC7Table_25_ok (by decide)
        X1 X2 X3 X4 h1F h2F h3F h4F hc1 hc2 hc3 hc4
        hne12 hne13 hne14 hne23 hne24 hne34 hd1 hd2 (he7.symm ▸ h3E) (he7.symm ▸ h4E)
  rcases hsome with hp | hp | hp
  · exact finish (g 0) (g 1) (g 2) (g 3)
      (hgSub 0) (hgSub 1) (hgSub 2) (hgSub 3) (hgF 0) (hgF 1) (hgF 2) (hgF 3)
      (hgCard 0) (hgCard 1) (hgCard 2) (hgCard 3)
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide))
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide)) hp
  · exact finish (g 0) (g 2) (g 1) (g 3)
      (hgSub 0) (hgSub 2) (hgSub 1) (hgSub 3) (hgF 0) (hgF 2) (hgF 1) (hgF 3)
      (hgCard 0) (hgCard 2) (hgCard 1) (hgCard 3)
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide))
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide)) hp
  · exact finish (g 1) (g 2) (g 0) (g 3)
      (hgSub 1) (hgSub 2) (hgSub 0) (hgSub 3) (hgF 1) (hgF 2) (hgF 0) (hgF 3)
      (hgCard 1) (hgCard 2) (hgCard 0) (hgCard 3)
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide))
      (hgNe (by decide)) (hgNe (by decide)) (hgNe (by decide)) hp

inductive RowSpec where
  | nonneg (d0 W : ℤ)
  | simpleNeg3 (d0 d3 W : ℤ)
  | neg235 (d0 d2 d3 W : ℤ)
  | row10 (d0 d3 d4 W d5 : ℤ)
  | lemma36 (d0 d3 d5 W : ℤ)
  | lemma37 (d0 d3 d5 d6 W : ℤ)

abbrev LayerChunks := List Nat × List (Nat × Int × Nat × List Nat)

def checkLayerSym (b k : Nat) (w_in : List Nat) (d_out t : Nat) (P_cl : List Nat)
    (swaps : List (Nat × Nat)) (ord : List Nat)
    (forbArr : Arr8 (Nat × List Nat)) (le : LayerChunks) : Bool :=
  match readExclChunks b k P_cl forbArr le.1 with
  | none => false
  | some cls =>
    let n2b := Nat.pow 2 b
    let mbits := mBitsFor P_cl.length
    let pMaskBig := listToMask P_cl
    let sp := buildSp16 b
    let smallZ := (List.range n2b).filter (fun u =>
      let c := Nat.add k (popCountAux b u)
      Nat.blt 0 c && Nat.blt c 3)
    let baseO := match Nat.beq k 0 with
      | true => 0 :: Nat.sub n2b 1 :: P_cl
      | false => [Nat.sub n2b 1]
    let pArr := listToArr8 P_cl
    let clArr := listToArr8 cls
    match buildInitVecs16 w_in 1 (Nat.mul d_out k) t n2b 0 with
    | (posBase, negBase, maxAbsC) =>
      listAll (fun tk =>
        match Nat.beq tk.1 0 with
        | true => checkTaskSym b mbits pMaskBig sp posBase negBase maxAbsC tk.2.1 swaps ord pArr clArr smallZ baseO tk.2.2.1 tk.2.2.2
        | false =>
          match Nat.beq tk.1 1 with
          | true => checkTaskSym b mbits pMaskBig sp posBase negBase maxAbsC tk.2.1 swaps ord pArr clArr (0 :: smallZ) baseO tk.2.2.1 tk.2.2.2
          | false =>
            match Nat.beq tk.1 2 with
            | false => false
            | true =>
              match listContainsNat smallZ 0 with
              | true => false
              | false => checkTaskSym b mbits pMaskBig sp posBase negBase maxAbsC tk.2.1 swaps ord pArr clArr smallZ (0 :: baseO) tk.2.2.1 tk.2.2.2) le.2

def hasLayerTaskSym (layers : List LayerChunks) (k ltag : ℕ) (tgt : ℤ) : Bool :=
  match listGet? layers k with
  | none => false
  | some le => listAny (fun tk => Nat.beq tk.1 ltag && decide (tk.2.1 = tgt)) le.2

def checkSpecTasksSym (b : ℕ) (spec : RowSpec) (layers : List LayerChunks) : Bool :=
  match spec with
  | RowSpec.nonneg d0 W =>
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers (12 - b) 0 W &&
    ((List.range (12 - b)).drop 1).all (fun k => hasLayerTaskSym layers k 0 0) &&
    decide (0 ≤ d0 + W)
  | RowSpec.simpleNeg3 d0 d3 W =>
    decide (5 ≤ b) &&
    decide (5 ≤ 12 - b) &&
    decide (d3 ≤ 0) &&
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers (12 - b) 0 W &&
    hasLayerTaskSym layers 3 1 0 &&
    hasLayerTaskSym layers 3 2 d3 &&
    ((List.range (12 - b)).drop 1).all (fun k => k == 3 || hasLayerTaskSym layers k 0 0) &&
    decide (0 ≤ d0 + (if 12 - b == 5 then 2 else 3 : ℤ) * d3 + W)
  | RowSpec.neg235 d0 d2 d3 W =>
    decide (b = 7) &&
    decide (d2 ≤ 0) &&
    decide (d3 ≤ 0) &&
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers 1 0 0 &&
    hasLayerTaskSym layers 2 0 d2 &&
    (if d3 == 0 then hasLayerTaskSym layers 3 0 0
     else hasLayerTaskSym layers 3 1 0 && hasLayerTaskSym layers 3 2 d3) &&
    hasLayerTaskSym layers 4 0 0 &&
    hasLayerTaskSym layers 5 0 W &&
    decide (0 ≤ d0 + 10 * d2 + 2 * d3 + W)
  | RowSpec.row10 d0 d3 d4 W d5 =>
    decide (b = 7) &&
    decide (d3 ≤ 0) &&
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers 1 0 0 &&
    hasLayerTaskSym layers 2 0 0 &&
    hasLayerTaskSym layers 3 1 0 &&
    hasLayerTaskSym layers 3 2 d3 &&
    hasLayerTaskSym layers 4 0 0 &&
    hasLayerTaskSym layers 4 2 d4 &&
    hasLayerTaskSym layers 5 0 W &&
    hasLayerTaskSym layers 5 2 d5 &&
    decide (0 ≤ d0 + d3 + W) &&
    decide (0 ≤ d0 + 2 * d3 + d4 + W) &&
    decide (0 ≤ d0 + 2 * d3 + d5)
  | RowSpec.lemma36 d0 d3 d5 W =>
    decide (b = 6) &&
    decide (d3 ≤ 0) &&
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers 1 0 0 &&
    hasLayerTaskSym layers 2 0 0 &&
    hasLayerTaskSym layers 3 1 0 &&
    hasLayerTaskSym layers 3 2 d3 &&
    hasLayerTaskSym layers 4 0 0 &&
    hasLayerTaskSym layers 5 0 0 &&
    hasLayerTaskSym layers 5 2 d5 &&
    hasLayerTaskSym layers 6 0 W &&
    decide (0 ≤ d0 + 2 * d3 + W) &&
    decide (0 ≤ d0 + 3 * d3 + d5 + W)
  | RowSpec.lemma37 d0 d3 d5 d6 W =>
    decide (b = 5) &&
    decide (d3 ≤ 0) &&
    hasLayerTaskSym layers 0 2 d0 &&
    hasLayerTaskSym layers 1 0 0 &&
    hasLayerTaskSym layers 2 0 0 &&
    hasLayerTaskSym layers 3 1 0 &&
    hasLayerTaskSym layers 3 2 d3 &&
    hasLayerTaskSym layers 4 0 0 &&
    hasLayerTaskSym layers 5 0 0 &&
    hasLayerTaskSym layers 5 2 d5 &&
    hasLayerTaskSym layers 6 0 0 &&
    hasLayerTaskSym layers 6 2 d6 &&
    hasLayerTaskSym layers 7 0 W &&
    decide (0 ≤ d0 + 2 * d3 + W) &&
    decide (0 ≤ d0 + 3 * d3 + d5 + W) &&
    decide (0 ≤ d0 + 3 * d3 + 2 * d6 + W)

def checkRowSym (b : Nat) (P_cl w_in : List Nat) (d_out t : Nat)
    (swaps : List (Nat × Nat)) (forb : List (Nat × List Nat)) (layers : List LayerChunks) : Bool :=
  let pMaskBig := listToMask P_cl
  match checkSwaps b w_in P_cl pMaskBig swaps with
  | false => false
  | true =>
    let ord := symOrd b w_in
    let fArr := listToArr8 forb
    listAll (fun k =>
      match listGet? layers k with
      | none => false
      | some le => checkLayerSym b k w_in d_out t P_cl swaps ord fArr le) (List.range (Nat.add (Nat.sub 12 b) 1))

def checkRowFull (b : Nat) (pm extra w_in : List Nat) (d_out t : Nat)
    (swaps : List (Nat × Nat)) (forb : List (Nat × List Nat))
    (spec : RowSpec) (layers : List LayerChunks) : Bool :=
  Nat.ble 3 b &&
  Nat.ble b 7 &&
  Nat.beq w_in.length b &&
  Nat.blt 0 t &&
  Nat.beq (Nat.add w_in.sum (Nat.mul (Nat.sub 12 b) d_out)) (Nat.mul 2 t) &&
  checkClosure pm extra &&
  listContainsNat (extra ++ pm) (Nat.sub (Nat.pow 2 b) 1) &&
  Nat.beq layers.length (Nat.add (Nat.sub 12 b) 1) &&
  checkSpecTasksSym b spec layers &&
  checkRowSym b (extra ++ pm) w_in d_out t swaps forb layers

lemma sum_subset_split {α : Type} [DecidableEq α] {P A B : Finset α} {f : α → ℤ}
    (hA : A ⊆ P) (hB : B ⊆ P) (hd : Disjoint A B)
    (hrest : ∀ x ∈ P, x ∉ A → x ∉ B → 0 ≤ f x) :
    (∑ x ∈ A, f x) + (∑ x ∈ B, f x) ≤ ∑ x ∈ P, f x := by
  have hu : (A ∪ B) ∪ (P \ (A ∪ B)) = P := union_sdiff_of_subset (union_subset hA hB)
  rw [← hu, sum_union disjoint_sdiff_self_right, sum_union hd]
  have hnn : 0 ≤ ∑ x ∈ P \ (A ∪ B), f x := by
    apply sum_nonneg; intro x hx
    obtain ⟨hxP, hnx⟩ := mem_sdiff.mp hx
    rw [mem_union, not_or] at hnx
    exact hrest x hxP hnx.1 hnx.2
  linarith

lemma sum_ge_card_mul_nonpos {α : Type} {S : Finset α} {f : α → ℤ} {d : ℤ} {m : ℕ}
    (hd : d ≤ 0) (hcard : S.card ≤ m) (hf : ∀ x ∈ S, d ≤ f x) :
    (m : ℤ) * d ≤ ∑ x ∈ S, f x := by
  have h1 : (S.card : ℤ) * d ≤ ∑ x ∈ S, f x := by
    calc (S.card : ℤ) * d = ∑ _ ∈ S, d := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ S, f x := sum_le_sum hf
  have h2 : (m : ℤ) * d ≤ (S.card : ℤ) * d :=
    mul_le_mul_of_nonpos_right (Nat.cast_le.mpr hcard) hd
  exact h2.trans h1

lemma layer_task_eval {b : ℕ} (hb : b ≤ 7) {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F) (hEmpty : ∅ ∈ F)
    (minSize : ∀ S ∈ F, S.Nonempty → 3 ≤ S.card)
    (e0 : Fin b ↪ Fin 12)
    (w_in : List ℕ) (hwlen : w_in.length = b) (d_out t : ℕ) (P_cl : List ℕ)
    (hPcl0 : ∀ m ∈ P_cl, (decode b m).map e0 ∈ F)
    (hfull : (2 ^ b - 1) ∈ P_cl)
    (swaps : List (ℕ × ℕ)) (hsw : checkSwaps b w_in P_cl (listToMask P_cl) swaps = true)
    (forbidden : List (ℕ × List ℕ)) (hno : ∀ p ∈ forbidden, ¬ HasPattern p.1 p.2 F)
    (layers : List LayerChunks)
    (hallL : ∀ k ∈ List.range (12 - b + 1),
      match listGet? layers k with
      | none => False
      | some le => checkLayerSym b k w_in d_out t P_cl swaps (symOrd b w_in) (listToArr8 forbidden) le = true)
    (K : Finset (Fin 12)) (hKsub0 : K ⊆ univ \ (univ.map e0))
    (ltag : ℕ) (tgt : ℤ)
    (htask : hasLayerTaskSym layers K.card ltag tgt = true) :
    let B := (univ : Finset (Fin b)).map e0
    let wF (j : Fin b) : ℕ := w_in.getD j.val 0
    let w (x : Fin 12) : ℕ := (∑ j : Fin b, if e0 j = x then wF j else 0) + (if x ∈ B then 0 else d_out)
    let Phi := ∑ Y ∈ F.filter (fun Y => Y \ B = K), ((∑ x ∈ Y, (w x : ℤ)) - (t : ℤ))
    (ltag = 0 → (∃ Y ∈ F, Y \ B = K) → tgt ≤ Phi) ∧
    (ltag = 1 → K ∉ F → (∃ Y ∈ F, Y \ B = K) → tgt ≤ Phi) ∧
    (ltag = 2 → K ∈ F → tgt ≤ Phi) := by
  classical
  intro B wF w Phi
  set k := K.card
  set ord := symOrd b w_in
  obtain ⟨e, heB, hew, hPcl, hSym_raw⟩ := exists_sym_canonical_emb F K e0 w_in P_cl swaps ord hPcl0 hsw
  have hKsub : K ⊆ univ \ (univ.map e) := by rwa [heB]
  have hk_le : k ≤ 12 - b := by
    have h1 := card_le_card hKsub0
    have hBsub : B ⊆ univ := subset_univ _
    have hBcard : B.card = b := by simp [B]
    rw [card_sdiff_of_subset hBsub, card_univ, Fintype.card_fin, hBcard] at h1
    exact h1
  have hk_mem : k ∈ List.range (12 - b + 1) := List.mem_range.mpr (by omega)
  have hLk := hallL k hk_mem
  dsimp [hasLayerTaskSym] at htask
  cases hget : listGet? layers k with
  | none => rw [hget] at htask; cases htask
  | some le =>
    rw [hget] at htask hLk
    simp only [listAny_iff, Bool.and_eq_true, nat_beq_true, decide_eq_true_eq] at htask
    obtain ⟨tk, htk_mem, rfl, rfl⟩ := htask
    dsimp only [checkLayerSym] at hLk
    cases hex : readExclChunks b k P_cl (listToArr8 forbidden) le.1 with
    | none => rw [hex] at hLk; cases hLk
    | some cls =>
      rw [hex] at hLk
      have hiv := buildInitVecs16_spec w_in 1 (d_out * k) t (2 ^ b) 0
      dsimp only at hiv
      rcases hbv : buildInitVecs16 w_in 1 (Nat.mul d_out k) t (Nat.pow 2 b) 0 with ⟨posBase, negBase, maxAbsC⟩
      rw [hbv] at hLk; dsimp only at hLk
      rw [nat_mul_eq, nat_pow_eq] at hbv; rw [hbv] at hiv
      simp only [pow_zero, one_mul, zero_add] at hiv
      have htk_ok := (listAll_iff _ le.2).mp hLk tk htk_mem
      obtain ⟨ucD, forceD, cardX, sumD⟩ := slice_general F e K closed hKsub
      let D := (univ : Finset (Finset (Fin b))).filter (fun U => K ∪ U.map e ∈ F)
      have hPhi_eq : Phi = ∑ U ∈ D, ((∑ j ∈ U, (wF j : ℤ)) + (d_out : ℤ) * (k : ℤ) - (t : ℤ)) := by
        calc Phi = ∑ Y ∈ F.filter (fun Y => Y \ (univ.map e) = K),
              ((∑ j ∈ univ.filter (fun j : Fin b => e j ∈ Y), (wF j : ℤ)) + (d_out : ℤ) * (k : ℤ) - (t : ℤ)) := by
              have hBeq : B = univ.map e := heB.symm
              dsimp only [Phi]
              rw [hBeq]
              apply sum_congr rfl; intro Y hY
              have hYB : (Y \ (univ.map e)).card = k := by rw [(mem_filter.mp hY).2]
              have hwY : ∑ x ∈ Y, (w x : ℤ) =
                  (∑ j ∈ univ.filter (fun j : Fin b => e j ∈ Y), (wF j : ℤ)) + (d_out : ℤ) * (k : ℤ) := by
                have hw_eq : ∀ x, w x = (∑ j : Fin b, if e j = x then wF j else 0) + (if x ∈ univ.map e then 0 else d_out) := by
                  intro x; dsimp [w, B]; rw [hew x, heB]
                simp_rw [hw_eq]
                push_cast
                rw [sum_add_distrib]
                have hi := congrArg (Nat.cast (R := ℤ)) (inner_weight_sum e wF Y)
                have ho := congrArg (Nat.cast (R := ℤ)) (outer_weight_sum (univ.map e) Y d_out)
                push_cast at hi ho
                rw [hi, ho, hYB]; ring
              rw [hwY]
          _ = _ := sumD (fun U => (∑ j ∈ U, (wF j : ℤ)) + (d_out : ℤ) * (k : ℤ) - (t : ℤ))
      let v (i : ℕ) : ℤ := if decode b i ∈ D then 1 else 0
      let p0 (u : ℕ) : ℕ := maskWeightRec w_in u + d_out * k - t
      let q0 (u : ℕ) : ℕ := t - (maskWeightRec w_in u + d_out * k)
      have run_nonempty (hneD : D.Nonempty)
          (zL oL : List ℕ) (hzL : ∀ u ∈ zL, v u = 0) (hoL : ∀ u ∈ oL, v u = 1)
          (hchk : checkTaskSym b (mBitsFor P_cl.length) (listToMask P_cl) (buildSp16 b)
            posBase negBase maxAbsC tk.2.1 swaps ord (listToArr8 P_cl) (listToArr8 cls)
            zL oL tk.2.2.1 tk.2.2.2 = true) :
          tk.2.1 ≤ Phi := by
        rw [hPhi_eq]
        obtain ⟨hall, hnd⟩ := range_decode_bijection hb
        rw [FranklLocal.indexed_sum D (List.range (2 ^ b)) (decode b) _ hall hnd]
        have bit (i : ℕ) : v i = 0 ∨ v i = 1 := by dsimp [v]; split_ifs <;> simp
        have join := FranklLocal.indicator_join D ucD (decode b) (FranklLocal.decode_union b)
        have force (m : ℕ) (hm : m ∈ P_cl) : ∀ i, v i ≤ v (i ||| m) :=
          FranklLocal.indicator_force D (decode b) (FranklLocal.decode_union b) (forceD (decode b m) (hPcl m hm))
        have hexcl : ∀ cl ∈ cls, (cl.map v).sum ≤ (cl.length : ℤ) - 1 := by
          dsimp only [readExclChunks] at hex
          set rv := readVint32 (B32.mk 0 0 (chunksToWords32 le.1))
          have hsnd := readExclLoop_sound e K hKsub rfl P_cl hPcl forbidden hno rv.1 rv.2 cls hex
          intro cl hcl
          have hv_eq : (fun i => if K ∪ (decode b i).map e ∈ F then (1 : ℤ) else 0) = v := by
            funext i; dsimp [v, D]; simp
          rw [← hv_eq]
          exact hsnd cl hcl
        have hSym : ∀ ij ∈ swaps,
            lexVal (fun u => decide (v (swapBit ij.1 ij.2 u) = 1)) ord ≤
              lexVal (fun u => decide (v u = 1)) ord := by
          intro ij hij
          have hdec_eq : ∀ u, decide (v u = 1) = decide (K ∪ (decode b u).map e ∈ F) := by
            intro u; dsimp [v, D]; by_cases h : K ∪ (decode b u).map e ∈ F <;> simp [h]
          simp_rw [hdec_eq]
          exact hSym_raw ij hij
        have hts := checkTaskSym_sound b (mBitsFor P_cl.length) posBase negBase maxAbsC p0 q0
          hiv.1 hiv.2.1 hiv.2.2 tk.2.1 P_cl cls swaps ord zL oL tk.2.2.1 tk.2.2.2 v
          bit join force hexcl hSym hzL hoL hchk
        have hvsum : vecSumZ p0 q0 v (2 ^ b) 0 =
            ((List.range (2 ^ b)).map (fun i => ((∑ j ∈ decode b i, (wF j : ℤ)) + (d_out : ℤ) * (k : ℤ) - (t : ℤ)) * v i)).sum := by
          apply vecSumZ_eq_list_sum
          intro u _
          have hm := maskWeightRec_eq_sum w_in b u hwlen
          dsimp [p0, q0, wF]
          omega
        rw [hvsum] at hts
        exact hts
      let smallZ := (List.range (Nat.pow 2 b)).filter (fun u =>
        let c := Nat.add k (popCountAux b u)
        Nat.blt 0 c && Nat.blt c 3)
      let baseO := match Nat.beq k 0 with
        | true => 0 :: Nat.sub (Nat.pow 2 b) 1 :: P_cl
        | false => [Nat.sub (Nat.pow 2 b) 1]
      have hsmallZ : ∀ u ∈ smallZ, v u = 0 := by
        intro u hu
        simp only [smallZ, List.mem_filter, List.mem_range, Bool.and_eq_true,
          nat_pow_eq, nat_add_eq, nat_blt_true] at hu
        rw [popCountAux_eq_card hb hu.1] at hu
        dsimp [v, D]
        rw [if_neg]
        simp only [mem_filter, mem_univ, true_and]
        intro hinF
        have hpos_c : 0 < (K ∪ (decode b u).map e).card := by rw [cardX]; exact hu.2.1
        have hlt3 : (K ∪ (decode b u).map e).card < 3 := by rw [cardX]; exact hu.2.2
        have hge3 := minSize _ hinF (card_pos.mp hpos_c)
        omega
      have hbaseO (hneD : D.Nonempty) : ∀ u ∈ baseO, v u = 1 := by
        have hunivF : (univ : Finset (Fin b)).map e ∈ F := by
          rw [← decode_two_pow_sub_one b]; exact hPcl _ hfull
        have htop : univ ∈ D := FranklGlobal.nonempty_full D hneD (forceD univ hunivF)
        intro u hu
        dsimp only [baseO] at hu
        cases hk0 : Nat.beq k 0
        · rw [hk0] at hu
          simp only [List.mem_singleton, nat_sub_eq, nat_pow_eq] at hu
          subst hu; dsimp [v]; rw [decode_two_pow_sub_one, if_pos htop]
        · rw [hk0] at hu
          have hK0 : K = ∅ := card_eq_zero.mp (Nat.beq_eq.mp hk0)
          rcases List.mem_cons.mp hu with rfl | hu1
          · dsimp [v, D]; rw [if_pos]; simp [decode_zero, hK0, hEmpty]
          rcases List.mem_cons.mp hu1 with rfl | huP
          · change (if decode b (2 ^ b - 1) ∈ D then (1 : ℤ) else 0) = 1
            rw [decode_two_pow_sub_one, if_pos htop]
          · dsimp [v, D]; rw [if_pos]; simp [hK0, hPcl u huP]
      have hne_of_wit (hwit : ∃ Y ∈ F, Y \ B = K) : D.Nonempty := by
        obtain ⟨Y, hYF, hYBK⟩ := hwit
        dsimp only [B] at hYBK
        rw [← heB] at hYBK
        refine ⟨univ.filter (fun j : Fin b => e j ∈ Y), ?_⟩
        simp only [D, mem_filter, mem_univ, true_and]
        have hKeq : K ∪ (univ.filter (fun j : Fin b => e j ∈ Y)).map e = Y := by
          ext a; simp only [mem_union, mem_map, mem_filter, mem_univ, true_and]
          by_cases haB : a ∈ univ.map e
          · obtain ⟨j, _, rfl⟩ := mem_map.mp haB
            have hnK : e j ∉ K := fun hm => (mem_sdiff.mp (hKsub hm)).2 haB
            simp [hnK]
          · have haK : a ∈ K ↔ a ∈ Y := by rw [← hYBK]; simp [haB]
            have hnM : ¬ ∃ j : Fin b, e j ∈ Y ∧ e j = a := by
              rintro ⟨j, _, rfl⟩; exact haB (mem_map.mpr ⟨j, mem_univ _, rfl⟩)
            simp [haK, hnM]
        rwa [hKeq]
      refine ⟨?_, ?_, ?_⟩
      · intro h0 hwit
        rw [h0] at htk_ok; dsimp only at htk_ok
        have hneD := hne_of_wit hwit
        exact run_nonempty hneD smallZ baseO hsmallZ (hbaseO hneD) htk_ok
      · intro h1 hKnotF hwit
        rw [h1] at htk_ok; dsimp only at htk_ok
        have hneD := hne_of_wit hwit
        have hz0 : ∀ u ∈ 0 :: smallZ, v u = 0 := by
          intro u hu
          rcases List.mem_cons.mp hu with rfl | hus
          · dsimp [v, D]; rw [if_neg]; simp [decode_zero, hKnotF]
          · exact hsmallZ u hus
        exact run_nonempty hneD (0 :: smallZ) baseO hz0 (hbaseO hneD) htk_ok
      · intro h2 hKinF
        rw [h2] at htk_ok; dsimp only at htk_ok
        cases hc0 : listContainsNat smallZ 0
        · rw [hc0] at htk_ok; dsimp only at htk_ok
          have hneD : D.Nonempty := ⟨∅, by simp [D, hKinF]⟩
          have ho0 : ∀ u ∈ 0 :: baseO, v u = 1 := by
            intro u hu
            rcases List.mem_cons.mp hu with rfl | hub
            · dsimp [v, D]; rw [if_pos]; simp [decode_zero, hKinF]
            · exact hbaseO hneD u hub
          exact run_nonempty hneD smallZ (0 :: baseO) hsmallZ ho0 htk_ok
        · rw [hc0] at htk_ok; cases htk_ok

lemma row_full_sound {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F) (hEmpty : ∅ ∈ F) (hUniv : univ ∈ F)
    (minSize : ∀ S ∈ F, S.Nonempty → 3 ≤ S.card)
    (hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F)
    {b : ℕ} {pm extra w_in : List ℕ} {d_out t : ℕ}
    {swaps : List (ℕ × ℕ)} {forbidden : List (ℕ × List ℕ)}
    (hnoForb : ∀ p ∈ forbidden, ¬ HasPattern p.1 p.2 F)
    {spec : RowSpec} {layers : List LayerChunks}
    (hok : checkRowFull b pm extra w_in d_out t swaps forbidden spec layers = true)
    (hpat : HasPattern b pm F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  classical
  simp only [checkRowFull, Bool.and_eq_true, nat_ble_true, nat_beq_true, nat_blt_true,
    nat_add_eq, nat_mul_eq, nat_sub_eq, nat_pow_eq, listContainsNat_iff] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb3, hb7⟩, hwlen⟩, htpos⟩, hwsum⟩, hcl⟩, hfull⟩, _hlenL⟩, hspec⟩, hrow⟩ := hok
  dsimp only [checkRowSym] at hrow
  cases hsw : checkSwaps b w_in (extra ++ pm) (listToMask (extra ++ pm)) swaps
  · rw [hsw] at hrow; cases hrow
  · rw [hsw] at hrow; dsimp only at hrow
    obtain ⟨e0, he0⟩ := hpat
    have hPcl0 := closure_mem closed e0 pm extra he0 hcl
    let B := (univ : Finset (Fin b)).map e0
    let E := (univ : Finset (Fin 12)) \ B
    have hBcard : B.card = b := by simp [B]
    have hEcard : E.card = 12 - b := by
      rw [card_sdiff_of_subset (subset_univ B), card_univ, Fintype.card_fin, hBcard]
    let wF (j : Fin b) : ℕ := w_in.getD j.val 0
    let w (x : Fin 12) : ℕ := (∑ j : Fin b, if e0 j = x then wF j else 0) + (if x ∈ B then 0 else d_out)
    have htot : (∑ i : Fin 12, w i) = 2 * t := by
      dsimp only [w]
      rw [sum_add_distrib]
      have h1 := inner_weight_sum e0 wF univ
      have h2 : univ.filter (fun j : Fin b => e0 j ∈ (univ : Finset (Fin 12))) = univ := by ext; simp
      rw [h2, finRange_sum_getD b w_in hwlen] at h1
      have h3 := outer_weight_sum B univ d_out
      have h3' : (∑ x : Fin 12, if x ∈ B then 0 else d_out) = (12 - b) * d_out := by
        rw [h3]; exact congrArg (· * d_out) hEcard
      rw [h1, h3', hwsum]
    refine ⟨w, by omega, ?_⟩
    rw [htot]
    suffices hnonneg : (0 : ℤ) ≤ ∑ Y ∈ F, ((∑ i ∈ Y, (w i : ℤ)) - (t : ℤ)) by
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at hnonneg
      have hcast : (F.card : ℤ) * (2 * (t : ℤ)) ≤ 2 * ∑ Y ∈ F, ∑ i ∈ Y, (w i : ℤ) := by linarith
      exact_mod_cast hcast
    let P := E.powerset
    let Phi (K : Finset (Fin 12)) : ℤ := ∑ Y ∈ F.filter (fun Y => Y \ B = K), ((∑ x ∈ Y, (w x : ℤ)) - (t : ℤ))
    have hpart : (∑ K ∈ P, Phi K) = ∑ Y ∈ F, ((∑ i ∈ Y, (w i : ℤ)) - (t : ℤ)) := by
      apply sum_fiberwise_of_maps_to
      intro Y _
      exact mem_powerset.mpr (sdiff_subset_sdiff (subset_univ Y) (Subset.refl B))
    rw [← hpart]
    have hallL := (listAll_iff _ (List.range (12 - b + 1))).mp (by simpa [nat_add_eq, nat_sub_eq] using hrow)
    have hhallL : ∀ k ∈ List.range (12 - b + 1),
        match listGet? layers k with
        | none => False
        | some le => checkLayerSym b k w_in d_out t (extra ++ pm) swaps (symOrd b w_in) (listToArr8 forbidden) le = true := by
      intro k hk
      have h := hallL k hk
      cases hlk : listGet? layers k with
      | none => rw [hlk] at h; cases h
      | some le => rw [hlk] at h; exact h
    have bk0 (d0 : ℤ) (htk : hasLayerTaskSym layers 0 2 d0 = true) : d0 ≤ Phi ∅ := by
      have h := layer_task_eval hb7 closed hEmpty minSize e0 w_in hwlen d_out t (extra ++ pm) hPcl0 hfull
        swaps hsw forbidden hnoForb layers hhallL ∅ (empty_subset E) 2 d0 (by simpa using htk)
      exact h.2.2 rfl hEmpty
    have btop (W : ℤ) (htk : hasLayerTaskSym layers (12 - b) 0 W = true) : W ≤ Phi E := by
      have h := layer_task_eval hb7 closed hEmpty minSize e0 w_in hwlen d_out t (extra ++ pm) hPcl0 hfull
        swaps hsw forbidden hnoForb layers hhallL E (Subset.refl E) 0 W (by simpa [hEcard] using htk)
      exact h.1 rfl ⟨univ, hUniv, rfl⟩
    have bin {K : Finset (Fin 12)} (hKP : K ∈ P) (d : ℤ)
        (htk : hasLayerTaskSym layers K.card 2 d = true) (hKF : K ∈ F) : d ≤ Phi K := by
      have h := layer_task_eval hb7 closed hEmpty minSize e0 w_in hwlen d_out t (extra ++ pm) hPcl0 hfull
        swaps hsw forbidden hnoForb layers hhallL K (mem_powerset.mp hKP) 2 d htk
      exact h.2.2 rfl hKF
    have bout0 {K : Finset (Fin 12)} (hKP : K ∈ P)
        (htk : hasLayerTaskSym layers K.card 1 0 = true) (hKnF : K ∉ F) : 0 ≤ Phi K := by
      by_cases hwit : ∃ Y ∈ F, Y \ B = K
      · have h := layer_task_eval hb7 closed hEmpty minSize e0 w_in hwlen d_out t (extra ++ pm) hPcl0 hfull
          swaps hsw forbidden hnoForb layers hhallL K (mem_powerset.mp hKP) 1 0 htk
        exact h.2.1 rfl hKnF hwit
      · simp only [Phi]
        have hem : F.filter (fun Y => Y \ B = K) = ∅ :=
          filter_eq_empty_iff.mpr (fun Y hYF hYBK => hwit ⟨Y, hYF, hYBK⟩)
        rw [hem, sum_empty]
    have bany {K : Finset (Fin 12)} (hKP : K ∈ P) (d : ℤ) (hd : d ≤ 0)
        (htk : hasLayerTaskSym layers K.card 0 d = true) : d ≤ Phi K := by
      by_cases hwit : ∃ Y ∈ F, Y \ B = K
      · have h := layer_task_eval hb7 closed hEmpty minSize e0 w_in hwlen d_out t (extra ++ pm) hPcl0 hfull
          swaps hsw forbidden hnoForb layers hhallL K (mem_powerset.mp hKP) 0 d htk
        exact h.1 rfl hwit
      · simp only [Phi]
        have hem : F.filter (fun Y => Y \ B = K) = ∅ :=
          filter_eq_empty_iff.mpr (fun Y hYF hYBK => hwit ⟨Y, hYF, hYBK⟩)
        rw [hem, sum_empty]; exact hd
    have h0P : (∅ : Finset (Fin 12)) ∈ P := empty_mem_powerset E
    have hEP : E ∈ P := mem_powerset_self E
    have h0neE : (∅ : Finset (Fin 12)) ≠ E := by
      intro heq; have := congrArg Finset.card heq; simp [hEcard] at this; omega
    have hmid_mem {K : Finset (Fin 12)} (hKP : K ∈ P) (hne0 : K ≠ ∅) (hneE : K ≠ E) :
        K.card ∈ (List.range (12 - b)).drop 1 := by
      have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne0)
      have hlt : K.card < 12 - b := by
        have hle := card_le_card (mem_powerset.mp hKP)
        rw [hEcard] at hle
        by_contra! hge
        exact hneE (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
      have hm_le : 12 - b ≤ 9 := by omega
      set kk := K.card
      set mm := 12 - b
      interval_cases mm <;> interval_cases kk <;> decide
    let K3 := P.filter (fun K => K.card = 3 ∧ K ∈ F)
    have hK3sub : K3 ⊆ P := filter_subset _ P
    cases spec with
    | nonneg d0 W =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨ht0, htW⟩, hmid⟩, hsum0⟩ := hspec
      have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl; exact h0P; exact hEP
      have hsp := sum_subset_split hsub0E (empty_subset P) (disjoint_empty_right _) (fun K hKP hn0E _ => by
        simp only [mem_insert, mem_singleton, not_or] at hn0E
        exact bany hKP 0 le_rfl (hmid K.card (hmid_mem hKP hn0E.1 hn0E.2)))
      rw [sum_pair h0neE, sum_empty, add_zero] at hsp
      have := bk0 d0 ht0; have := btop W htW; linarith
    | simpleNeg3 d0 d3 W =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb5, hm5⟩, hd3le⟩, ht0⟩, htW⟩, ht3f⟩, ht3t⟩, hmid⟩, hsum0⟩ := hspec
      have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl; exact h0P; exact hEP
      have hdisj : Disjoint ({∅, E} : Finset (Finset (Fin 12))) K3 := by
        apply disjoint_left.mpr; intro x hx hx3
        have hc3 := (mem_filter.mp hx3).2.1
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp at hc3
        · rw [hEcard] at hc3; omega
      have hsp := sum_subset_split hsub0E hK3sub hdisj (fun K hKP hn0E hnK3 => by
        simp only [mem_insert, mem_singleton, not_or] at hn0E
        rcases hmid K.card (hmid_mem hKP hn0E.1 hn0E.2) with hk3 | htk0
        · have hKnF : K ∉ F := fun hKF => hnK3 (mem_filter.mpr ⟨hKP, hk3, hKF⟩)
          exact bout0 hKP (hk3 ▸ ht3f) hKnF
        · exact bany hKP 0 le_rfl htk0)
      rw [sum_pair h0neE] at hsp
      have hK3in : ∀ K ∈ K3, d3 ≤ Phi K := fun K hK =>
        bin (mem_filter.mp hK).1 d3 ((mem_filter.mp hK).2.1 ▸ ht3t) (mem_filter.mp hK).2.2
      by_cases hm5eq : 12 - b = 5
      · rw [if_pos hm5eq] at hsum0
        have hc2 : K3.card ≤ 2 := no_three_3sets_in_5_card hnoFC E (by rw [hEcard]; omega)
        have h3sum : ((2 : ℕ) : ℤ) * d3 ≤ ∑ x ∈ K3, Phi x := sum_ge_card_mul_nonpos hd3le hc2 hK3in
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W htW; linarith
      · rw [if_neg hm5eq] at hsum0
        have hc3 : K3.card ≤ 3 := no_four_3sets_in_7 hnoFC E (by rw [hEcard]; omega)
        have h3sum : ((3 : ℕ) : ℤ) * d3 ≤ ∑ x ∈ K3, Phi x := sum_ge_card_mul_nonpos hd3le hc3 hK3in
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W htW; linarith
    | neg235 d0 d2 d3 W =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_eq, hd2le⟩, hd3le⟩, ht0⟩, ht1⟩, ht2⟩, ht3⟩, ht4⟩, ht5⟩, hsum0⟩ := hspec
      subst hb_eq
      have hE5 : E.card = 5 := hEcard
      let P2 := E.powersetCard 2
      have hP2sub : P2 ⊆ P := fun K hK => mem_powerset.mpr (mem_powersetCard.mp hK).1
      have hP2card : P2.card ≤ 10 := by
        have heq10 : (E.powersetCard 2).card = 10 := by rw [card_powersetCard, hE5]; decide
        exact le_of_eq heq10
      have hAsub : ({∅, E} ∪ P2 : Finset (Finset (Fin 12))) ⊆ P := by
        apply union_subset
        · intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl; exact h0P; exact hEP
        · exact hP2sub
      have hd0EP2 : Disjoint ({∅, E} : Finset (Finset (Fin 12))) P2 := by
        apply disjoint_left.mpr; intro x hx hx2
        have hc2 := (mem_powersetCard.mp hx2).2
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hE5] at hc2
      have hdAK3 : Disjoint ({∅, E} ∪ P2 : Finset (Finset (Fin 12))) K3 := by
        apply disjoint_left.mpr; intro x hx hx3
        have hc3 := (mem_filter.mp hx3).2.1
        simp only [mem_union, mem_insert, mem_singleton] at hx
        rcases hx with (rfl | rfl) | hx2
        · simp at hc3
        · rw [hE5] at hc3; omega
        · have hc2 := (mem_powersetCard.mp hx2).2; omega
      have hP2sum : ((10 : ℕ) : ℤ) * d2 ≤ ∑ K ∈ P2, Phi K :=
        sum_ge_card_mul_nonpos hd2le hP2card (fun K hK =>
          bany (hP2sub hK) d2 hd2le ((mem_powersetCard.mp hK).2 ▸ ht2))
      push_cast at hP2sum
      by_cases hd3z : d3 = 0
      · subst hd3z
        simp only [beq_self_eq_true, ↓reduceIte] at ht3
        have hsp := sum_subset_split (f := Phi) hAsub (empty_subset P) (disjoint_empty_right _) (fun K hKP hnA _ => by
          simp only [mem_union, mem_insert, mem_singleton, not_or] at hnA
          have hle5 : K.card ≤ 5 := by have h := card_le_card (mem_powerset.mp hKP); rwa [hE5] at h
          have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hnA.1.1)
          have hlt5 : K.card < 5 := by
            by_contra! hge; exact hnA.1.2 (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
          have hne2 : K.card ≠ 2 := fun h2 => hnA.2 (mem_powersetCard.mpr ⟨mem_powerset.mp hKP, h2⟩)
          have hcases : K.card = 1 ∨ K.card = 3 ∨ K.card = 4 := by omega
          rcases hcases with hk | hk | hk
          · exact bany hKP 0 le_rfl (hk ▸ ht1)
          · exact bany hKP 0 le_rfl (hk ▸ ht3)
          · exact bany hKP 0 le_rfl (hk ▸ ht4))
        rw [sum_union hd0EP2, sum_pair h0neE, sum_empty, add_zero] at hsp
        have := bk0 d0 ht0; have := btop W ht5; linarith
      · have hfalse : (d3 == 0) = false := beq_false_of_ne hd3z
        rw [hfalse] at ht3; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at ht3
        have hsp := sum_subset_split (f := Phi) hAsub hK3sub hdAK3 (fun K hKP hnA hnK3 => by
          simp only [mem_union, mem_insert, mem_singleton, not_or] at hnA
          have hle5 : K.card ≤ 5 := by have h := card_le_card (mem_powerset.mp hKP); rwa [hE5] at h
          have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hnA.1.1)
          have hlt5 : K.card < 5 := by
            by_contra! hge; exact hnA.1.2 (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
          have hne2 : K.card ≠ 2 := fun h2 => hnA.2 (mem_powersetCard.mpr ⟨mem_powerset.mp hKP, h2⟩)
          have hcases : K.card = 1 ∨ K.card = 3 ∨ K.card = 4 := by omega
          rcases hcases with hk | hk | hk
          · exact bany hKP 0 le_rfl (hk ▸ ht1)
          · have hKnF : K ∉ F := fun hKF => hnK3 (mem_filter.mpr ⟨hKP, hk, hKF⟩)
            exact bout0 hKP (hk ▸ ht3.1) hKnF
          · exact bany hKP 0 le_rfl (hk ▸ ht4))
        rw [sum_union hd0EP2, sum_pair h0neE] at hsp
        have hc2 : K3.card ≤ 2 := no_three_3sets_in_5_card hnoFC E (by rw [hE5])
        have h3sum : ((2 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc2 (fun K hK =>
          bin (mem_filter.mp hK).1 d3 ((mem_filter.mp hK).2.1 ▸ ht3.2) (mem_filter.mp hK).2.2)
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W ht5; linarith
    | row10 d0 d3 d4 W d5 =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_eq, hd3le⟩, ht0⟩, ht1⟩, ht2⟩, ht3f⟩, ht3t⟩, ht4⟩, ht4in⟩, ht5⟩, ht5in⟩, hs1⟩, hs2⟩, hs3⟩ := hspec
      subst hb_eq
      have hE5 : E.card = 5 := hEcard
      have hc2 : K3.card ≤ 2 := no_three_3sets_in_5_card hnoFC E (by rw [hE5])
      have hK3in : ∀ K ∈ K3, d3 ≤ Phi K := fun K hK =>
        bin (mem_filter.mp hK).1 d3 ((mem_filter.mp hK).2.1 ▸ ht3t) (mem_filter.mp hK).2.2
      have hrest0 (K : Finset (Fin 12)) (hKP : K ∈ P) (hne0 : K ≠ ∅) (hneE : K ≠ E) (hnK3 : K ∉ K3) : 0 ≤ Phi K := by
        have hle5 := card_le_card (mem_powerset.mp hKP); rw [hE5] at hle5
        have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne0)
        have hlt5 : K.card < 5 := by
          by_contra! hge; exact hneE (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
        have hcases : K.card = 1 ∨ K.card = 2 ∨ K.card = 3 ∨ K.card = 4 := by omega
        rcases hcases with hk | hk | hk | hk
        · exact bany hKP 0 le_rfl (hk ▸ ht1)
        · exact bany hKP 0 le_rfl (hk ▸ ht2)
        · exact bout0 hKP (hk ▸ ht3f) (fun hKF => hnK3 (mem_filter.mpr ⟨hKP, hk, hKF⟩))
        · exact bany hKP 0 le_rfl (hk ▸ ht4)
      by_cases hc_le1 : K3.card ≤ 1
      · have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl; exact h0P; exact hEP
        have hd0EK3 : Disjoint ({∅, E} : Finset (Finset (Fin 12))) K3 := by
          apply disjoint_left.mpr; intro x hx hx3
          have hc3 := (mem_filter.mp hx3).2.1
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [hE5] at hc3
        have hsp := sum_subset_split hsub0E hK3sub hd0EK3 (fun K hKP hn0E hnK3 => by
          simp only [mem_insert, mem_singleton, not_or] at hn0E
          exact hrest0 K hKP hn0E.1 hn0E.2 hnK3)
        rw [sum_pair h0neE] at hsp
        have h3sum : ((1 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc_le1 hK3in
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W ht5; linarith
      · have hc_eq2 : K3.card = 2 := by omega
        obtain ⟨A, C, hAC, hK3eq⟩ := card_eq_two.mp hc_eq2
        have hAm : A ∈ K3 := hK3eq ▸ mem_insert_self A {C}
        have hCm : C ∈ K3 := hK3eq ▸ mem_insert_of_mem (mem_singleton_self C)
        have hAF := (mem_filter.mp hAm).2.2; have hCF := (mem_filter.mp hCm).2.2
        have hcA := (mem_filter.mp hAm).2.1; have hcC := (mem_filter.mp hCm).2.1
        have hAE := mem_powerset.mp (mem_filter.mp hAm).1
        have hCE := mem_powerset.mp (mem_filter.mp hCm).1
        let U := A ∪ C
        have hUF : U ∈ F := closed A hAF C hCF
        have hUE : U ⊆ E := union_subset hAE hCE
        have hUP : U ∈ P := mem_powerset.mpr hUE
        have hbnd := union_pair_bounds hAC hcA hcC
        have hUle5 : U.card ≤ 5 := by have h := card_le_card hUE; rwa [hE5] at h
        have hUcases : U.card = 4 ∨ U.card = 5 := by change 4 ≤ U.card ∧ U.card ≤ 6 at hbnd; omega
        have h3sum : ((2 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc2 hK3in
        push_cast at h3sum
        rcases hUcases with hcU4 | hcU5
        · have hU0 : U ≠ ∅ := by intro h; rw [h] at hcU4; simp at hcU4
          have hUE_ne : U ≠ E := by intro h; rw [h, hE5] at hcU4; omega
          have hsubA : ({∅, U, E} : Finset (Finset (Fin 12))) ⊆ P := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl; exact h0P; exact hUP; exact hEP
          have hdAK3 : Disjoint ({∅, U, E} : Finset (Finset (Fin 12))) K3 := by
            apply disjoint_left.mpr; intro x hx hx3
            have hc3 := (mem_filter.mp hx3).2.1
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> simp [hcU4, hE5] at hc3
          have hsp := sum_subset_split hsubA hK3sub hdAK3 (fun K hKP hnA hnK3 => by
            simp only [mem_insert, mem_singleton, not_or] at hnA
            exact hrest0 K hKP hnA.1 hnA.2.2 hnK3)
          rw [sum_insert (by simp [h0neE, hU0.symm]), sum_pair hUE_ne] at hsp
          have hPhiU := bin hUP d4 (hcU4 ▸ ht4in) hUF
          have := bk0 d0 ht0; have := btop W ht5; linarith
        · have hUeqE : U = E := eq_of_subset_of_card_le hUE (by rw [hE5, hcU5])
          have hEF : E ∈ F := hUeqE ▸ hUF
          have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl; exact h0P; exact hEP
          have hd0EK3 : Disjoint ({∅, E} : Finset (Finset (Fin 12))) K3 := by
            apply disjoint_left.mpr; intro x hx hx3
            have hc3 := (mem_filter.mp hx3).2.1
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl <;> simp [hE5] at hc3
          have hsp := sum_subset_split hsub0E hK3sub hd0EK3 (fun K hKP hn0E hnK3 => by
            simp only [mem_insert, mem_singleton, not_or] at hn0E
            exact hrest0 K hKP hn0E.1 hn0E.2 hnK3)
          rw [sum_pair h0neE] at hsp
          have hPhiE := bin hEP d5 (hE5 ▸ ht5in) hEF
          have := bk0 d0 ht0; linarith
    | lemma36 d0 d3 d5 W =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_eq, hd3le⟩, ht0⟩, ht1⟩, ht2⟩, ht3f⟩, ht3t⟩, ht4⟩, ht5⟩, ht5in⟩, ht6⟩, hs1⟩, hs2⟩ := hspec
      subst hb_eq
      have hE6 : E.card = 6 := hEcard
      have hc3 : K3.card ≤ 3 := no_four_3sets_in_7 hnoFC E (by rw [hE6]; decide)
      have hK3in : ∀ K ∈ K3, d3 ≤ Phi K := fun K hK =>
        bin (mem_filter.mp hK).1 d3 ((mem_filter.mp hK).2.1 ▸ ht3t) (mem_filter.mp hK).2.2
      have hrest0 (K : Finset (Fin 12)) (hKP : K ∈ P) (hne0 : K ≠ ∅) (hneE : K ≠ E) (hnK3 : K ∉ K3) : 0 ≤ Phi K := by
        have hle6 := card_le_card (mem_powerset.mp hKP); rw [hE6] at hle6
        have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne0)
        have hlt6 : K.card < 6 := by
          by_contra! hge; exact hneE (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
        have hcases : K.card = 1 ∨ K.card = 2 ∨ K.card = 3 ∨ K.card = 4 ∨ K.card = 5 := by omega
        rcases hcases with hk | hk | hk | hk | hk
        · exact bany hKP 0 le_rfl (hk ▸ ht1)
        · exact bany hKP 0 le_rfl (hk ▸ ht2)
        · exact bout0 hKP (hk ▸ ht3f) (fun hKF => hnK3 (mem_filter.mpr ⟨hKP, hk, hKF⟩))
        · exact bany hKP 0 le_rfl (hk ▸ ht4)
        · exact bany hKP 0 le_rfl (hk ▸ ht5)
      by_cases hc_le2 : K3.card ≤ 2
      · have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl; exact h0P; exact hEP
        have hd0EK3 : Disjoint ({∅, E} : Finset (Finset (Fin 12))) K3 := by
          apply disjoint_left.mpr; intro x hx hx3
          have hc := (mem_filter.mp hx3).2.1
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [hE6] at hc
        have hsp := sum_subset_split hsub0E hK3sub hd0EK3 (fun K hKP hn0E hnK3 => by
          simp only [mem_insert, mem_singleton, not_or] at hn0E
          exact hrest0 K hKP hn0E.1 hn0E.2 hnK3)
        rw [sum_pair h0neE] at hsp
        have h3sum : ((2 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc_le2 hK3in
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W ht6; linarith
      · have hc_eq3 : K3.card = 3 := by omega
        obtain ⟨A, C, G, hAC, hAG, hCG, hK3eq⟩ := card_eq_three.mp hc_eq3
        have hAm : A ∈ K3 := hK3eq ▸ mem_insert_self A _
        have hCm : C ∈ K3 := hK3eq ▸ mem_insert_of_mem (mem_insert_self C _)
        have hGm : G ∈ K3 := hK3eq ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self G))
        have h6u := no_three_3sets_in_5 hnoFC A C G
          (mem_filter.mp hAm).2.2 (mem_filter.mp hCm).2.2 (mem_filter.mp hGm).2.2
          hAC hAG hCG (mem_filter.mp hAm).2.1 (mem_filter.mp hCm).2.1 (mem_filter.mp hGm).2.1
        have hl3 := lemma3_cards closed E A C G
          (mem_filter.mp hAm).2.2 (mem_filter.mp hCm).2.2 (mem_filter.mp hGm).2.2
          (mem_powerset.mp (mem_filter.mp hAm).1) (mem_powerset.mp (mem_filter.mp hCm).1) (mem_powerset.mp (mem_filter.mp hGm).1)
          hAC hAG hCG (mem_filter.mp hAm).2.1 (mem_filter.mp hCm).2.1 (mem_filter.mp hGm).2.1 h6u
        rcases hl3 with ⟨K5, hK5E, hcK5, hK5F⟩ | ⟨K6, K6', hK6E, hK6'E, hne6, hcK6, hcK6', _, _⟩
        · have hK5P : K5 ∈ P := mem_powerset.mpr hK5E
          have hK5_0 : K5 ≠ ∅ := by intro h; rw [h] at hcK5; simp at hcK5
          have hK5_E : K5 ≠ E := by intro h; rw [h, hE6] at hcK5; omega
          have hsubA : ({∅, K5, E} : Finset (Finset (Fin 12))) ⊆ P := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl; exact h0P; exact hK5P; exact hEP
          have hdAK3 : Disjoint ({∅, K5, E} : Finset (Finset (Fin 12))) K3 := by
            apply disjoint_left.mpr; intro x hx hx3
            have hc := (mem_filter.mp hx3).2.1
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> simp [hcK5, hE6] at hc
          have hsp := sum_subset_split hsubA hK3sub hdAK3 (fun K hKP hnA hnK3 => by
            simp only [mem_insert, mem_singleton, not_or] at hnA
            exact hrest0 K hKP hnA.1 hnA.2.2 hnK3)
          rw [sum_insert (by simp [h0neE, hK5_0.symm]), sum_pair hK5_E] at hsp
          have h3sum : ((3 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc3 hK3in
          push_cast at h3sum
          have hPhi5 := bin hK5P d5 (hcK5 ▸ ht5in) hK5F
          have := bk0 d0 ht0; have := btop W ht6; linarith
        · have heq1 : K6 = E := eq_of_subset_of_card_le hK6E (by rw [hE6, hcK6])
          have heq2 : K6' = E := eq_of_subset_of_card_le hK6'E (by rw [hE6, hcK6'])
          exact (hne6 (heq1.trans heq2.symm)).elim
    | lemma37 d0 d3 d5 d6 W =>
      simp only [checkSpecTasksSym, Bool.and_eq_true, decide_eq_true_eq] at hspec
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb_eq, hd3le⟩, ht0⟩, ht1⟩, ht2⟩, ht3f⟩, ht3t⟩, ht4⟩, ht5⟩, ht5in⟩, ht6⟩, ht6in⟩, ht7⟩, hs1⟩, hs2⟩, hs3⟩ := hspec
      subst hb_eq
      have hE7 : E.card = 7 := hEcard
      have hc3 : K3.card ≤ 3 := no_four_3sets_in_7 hnoFC E (by rw [hE7])
      have hK3in : ∀ K ∈ K3, d3 ≤ Phi K := fun K hK =>
        bin (mem_filter.mp hK).1 d3 ((mem_filter.mp hK).2.1 ▸ ht3t) (mem_filter.mp hK).2.2
      have hrest0 (K : Finset (Fin 12)) (hKP : K ∈ P) (hne0 : K ≠ ∅) (hneE : K ≠ E) (hnK3 : K ∉ K3) : 0 ≤ Phi K := by
        have hle7 := card_le_card (mem_powerset.mp hKP); rw [hE7] at hle7
        have hpos : 0 < K.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hne0)
        have hlt7 : K.card < 7 := by
          by_contra! hge; exact hneE (eq_of_subset_of_card_le (mem_powerset.mp hKP) (by omega))
        have hcases : K.card = 1 ∨ K.card = 2 ∨ K.card = 3 ∨ K.card = 4 ∨ K.card = 5 ∨ K.card = 6 := by omega
        rcases hcases with hk | hk | hk | hk | hk | hk
        · exact bany hKP 0 le_rfl (hk ▸ ht1)
        · exact bany hKP 0 le_rfl (hk ▸ ht2)
        · exact bout0 hKP (hk ▸ ht3f) (fun hKF => hnK3 (mem_filter.mpr ⟨hKP, hk, hKF⟩))
        · exact bany hKP 0 le_rfl (hk ▸ ht4)
        · exact bany hKP 0 le_rfl (hk ▸ ht5)
        · exact bany hKP 0 le_rfl (hk ▸ ht6)
      by_cases hc_le2 : K3.card ≤ 2
      · have hsub0E : ({∅, E} : Finset (Finset (Fin 12))) ⊆ P := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl; exact h0P; exact hEP
        have hd0EK3 : Disjoint ({∅, E} : Finset (Finset (Fin 12))) K3 := by
          apply disjoint_left.mpr; intro x hx hx3
          have hc := (mem_filter.mp hx3).2.1
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [hE7] at hc
        have hsp := sum_subset_split hsub0E hK3sub hd0EK3 (fun K hKP hn0E hnK3 => by
          simp only [mem_insert, mem_singleton, not_or] at hn0E
          exact hrest0 K hKP hn0E.1 hn0E.2 hnK3)
        rw [sum_pair h0neE] at hsp
        have h3sum : ((2 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc_le2 hK3in
        push_cast at h3sum
        have := bk0 d0 ht0; have := btop W ht7; linarith
      · have hc_eq3 : K3.card = 3 := by omega
        obtain ⟨A, C, G, hAC, hAG, hCG, hK3eq⟩ := card_eq_three.mp hc_eq3
        have hAm : A ∈ K3 := hK3eq ▸ mem_insert_self A _
        have hCm : C ∈ K3 := hK3eq ▸ mem_insert_of_mem (mem_insert_self C _)
        have hGm : G ∈ K3 := hK3eq ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self G))
        have h6u := no_three_3sets_in_5 hnoFC A C G
          (mem_filter.mp hAm).2.2 (mem_filter.mp hCm).2.2 (mem_filter.mp hGm).2.2
          hAC hAG hCG (mem_filter.mp hAm).2.1 (mem_filter.mp hCm).2.1 (mem_filter.mp hGm).2.1
        have hl3 := lemma3_cards closed E A C G
          (mem_filter.mp hAm).2.2 (mem_filter.mp hCm).2.2 (mem_filter.mp hGm).2.2
          (mem_powerset.mp (mem_filter.mp hAm).1) (mem_powerset.mp (mem_filter.mp hCm).1) (mem_powerset.mp (mem_filter.mp hGm).1)
          hAC hAG hCG (mem_filter.mp hAm).2.1 (mem_filter.mp hCm).2.1 (mem_filter.mp hGm).2.1 h6u
        have h3sum : ((3 : ℕ) : ℤ) * d3 ≤ ∑ K ∈ K3, Phi K := sum_ge_card_mul_nonpos hd3le hc3 hK3in
        push_cast at h3sum
        rcases hl3 with ⟨K5, hK5E, hcK5, hK5F⟩ | ⟨K6, K6', hK6E, hK6'E, hne6, hcK6, hcK6', hK6F, hK6'F⟩
        · have hK5P : K5 ∈ P := mem_powerset.mpr hK5E
          have hK5_0 : K5 ≠ ∅ := by intro h; rw [h] at hcK5; simp at hcK5
          have hK5_E : K5 ≠ E := by intro h; rw [h, hE7] at hcK5; omega
          have hsubA : ({∅, K5, E} : Finset (Finset (Fin 12))) ⊆ P := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl; exact h0P; exact hK5P; exact hEP
          have hdAK3 : Disjoint ({∅, K5, E} : Finset (Finset (Fin 12))) K3 := by
            apply disjoint_left.mpr; intro x hx hx3
            have hc := (mem_filter.mp hx3).2.1
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;> simp [hcK5, hE7] at hc
          have hsp := sum_subset_split hsubA hK3sub hdAK3 (fun K hKP hnA hnK3 => by
            simp only [mem_insert, mem_singleton, not_or] at hnA
            exact hrest0 K hKP hnA.1 hnA.2.2 hnK3)
          rw [sum_insert (by simp [h0neE, hK5_0.symm]), sum_pair hK5_E] at hsp
          have hPhi5 := bin hK5P d5 (hcK5 ▸ ht5in) hK5F
          have := bk0 d0 ht0; have := btop W ht7; linarith
        · have hK6P : K6 ∈ P := mem_powerset.mpr hK6E
          have hK6'P : K6' ∈ P := mem_powerset.mpr hK6'E
          have hK6_0 : K6 ≠ ∅ := by intro h; rw [h] at hcK6; simp at hcK6
          have hK6'_0 : K6' ≠ ∅ := by intro h; rw [h] at hcK6'; simp at hcK6'
          have hK6_E : K6 ≠ E := by intro h; rw [h, hE7] at hcK6; omega
          have hK6'_E : K6' ≠ E := by intro h; rw [h, hE7] at hcK6'; omega
          have hsubA : ({∅, K6, K6', E} : Finset (Finset (Fin 12))) ⊆ P := by
            intro x hx; simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl; exact h0P; exact hK6P; exact hK6'P; exact hEP
          have hdAK3 : Disjoint ({∅, K6, K6', E} : Finset (Finset (Fin 12))) K3 := by
            apply disjoint_left.mpr; intro x hx hx3
            have hc := (mem_filter.mp hx3).2.1
            simp only [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl <;> simp [hcK6, hcK6', hE7] at hc
          have hsp := sum_subset_split hsubA hK3sub hdAK3 (fun K hKP hnA hnK3 => by
            simp only [mem_insert, mem_singleton, not_or] at hnA
            exact hrest0 K hKP hnA.1 hnA.2.2.2 hnK3)
          rw [sum_insert (by simp [h0neE, hK6_0.symm, hK6'_0.symm]),
              sum_insert (by simp [hne6, hK6_E]), sum_pair hK6'_E] at hsp
          have hPhi6 := bin hK6P d6 (hcK6 ▸ ht6in) hK6F
          have hPhi6' := bin hK6'P d6 (hcK6' ▸ ht6in) hK6'F
          have := bk0 d0 ht0; have := btop W ht7; linarith

def allPats : List (Nat × List Nat) := [(4,[11,13,14]),(5,[25,26,28]),(5,[21,26,28]),(5,[7,26,28]),(6,[7,11,52,56]),(6,[7,25,42,52]),(7,[81,82,100,104]),(7,[49,82,100,104]),(7,[25,74,100,112]),(7,[25,88,98,100]),(7,[13,22,104,112]),(7,[13,28,98,112]),(7,[56,73,82,100]),(7,[13,50,84,104]),(5,[7,11,23]),(6,[7,57,58,60]),(6,[7,15,23,56]),(5,[7,25]),(6,[7,57,58]),(7,[7,15,23,39,71]),(6,[15,23,27,39,43,51]),(7,[15,23,39,71]),(6,[7,15,23,39]),(7,[7,15,23,104]),(6,[7,15,56]),(6,[15,23,39]),(5,[7,27,29]),(7,[7,121,122,124]),(6,[7,57,59]),(5,[15,23,27]),(6,[7,56]),(4,[7,11]),(6,[7,59,61]),(6,[7,57]),(5,[7,27]),(6,[7,59]),(7,[7,120]),(3,[7])]
def forbUpTo (n : Nat) : List (Nat × List Nat) := allPats.take n

lemma take_succ_mem {α : Type} : ∀ (l : List α) (n : ℕ) (v x : α),
    listGet? l n = some v → x ∈ l.take (n + 1) → x ∈ l.take n ∨ x = v
  | [], _, _, _, h, _ => by cases h
  | a :: _, 0, v, x, h, hx => by
    simp only [listGet?, Option.some.injEq] at h
    subst h
    simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hx
    exact Or.inr hx
  | a :: as, n + 1, v, x, h, hx => by
    simp only [List.take_succ_cons, List.mem_cons] at hx ⊢
    rcases hx with rfl | hmem
    · exact Or.inl (Or.inl rfl)
    · rcases take_succ_mem as n v x h hmem with h1 | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h2

lemma forb_extend {F : Finset (Finset (Fin 12))} (l : List (ℕ × List ℕ)) (n : ℕ) (q : ℕ × List ℕ)
    (hget : listGet? l n = some q)
    (hprev : ∀ p ∈ l.take n, ¬ HasPattern p.1 p.2 F)
    (hq : ¬ HasPattern q.1 q.2 F) :
    ∀ p ∈ l.take (n + 1), ¬ HasPattern p.1 p.2 F := by
  intro p hp
  rcases take_succ_mem l n q p hget hp with h1 | rfl
  · exact hprev p h1
  · exact hq

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc1_ok : checkFCFull 4 [11,13,14] [15] [1,1,1,1] 4 2 [0x142850a1432908206c482ac2] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc2_ok : checkFCFull 5 [25,26,28] [27,31,29,30] [2,2,2,3,3] 12 6 [0x2850a142d0e142bbe162be03a0700d81a03202e0050a162f0e142f0f179f40602850a1a061442031032020822811811011452831831191661545435844918989144980682] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc3_ok : checkFCFull 5 [21,26,28] [31,29,30] [2,2,3,3,4] 14 6 [0x142c50a1429ef146be03a0700d015013002850a162858bc3850b146d50a80c050a16870a1a28106145244124203183229105195555152d4550d55144491936090710c44d8180882] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc4_ok : checkFCFull 5 [7,26,28] [31,30] [1,2,2,2,2] 9 6 [0x1084210850f34850be038068038078010850b952855a6280c04210b142142850a1923244224204144124282182301291311844512344d924a980c4a5062294246d824310b4b10b82] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc5_ok : checkFCFull 6 [7,11,52,56] [15,63,55,59,60] [1,1,1,1,1,1] 6 10 [0xa142850a14644f80b805a022c00a142850a2d20a146a0380a14285161057c01d80dc01e00f022850a142c50a142c50a142852dc2851a80602850a1429d0a191309092620588221048421052308881520a84111025dda11a12a150f18541754246063584c84b84284a7477486446445624520510606505605700ca1541986116191909d1b82] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc6_ok : checkFCFull 6 [7,25,42,52] [31,63,47,55,59,61,62] [1,1,1,1,1,1] 6 2 [0x962d0f152d0f43a5a1e870a1687a1e8780150f43a54a96878a1680543d0f96870d0f43d0f43854a5a24480d1428205300c8692290e90a94a51e5165125065a211e11210a1c1d89d81d41d31d21d01d41901981505501561125118d9093094411482] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc7_ok : checkFCFull 7 [81,82,100,104] [83,119,127,123,117,125,121,118,126,122,108] [2,2,2,2,3,3,5] 19 18 [0x842604854a03069ad1c6933a0d6828951458ac589c4c704c5c69c9be4cf24f9a7a9ad4aeb971878c1c5a62c31498a2c49e30ad4b6d04541a20d5cb41f88fe64460f5a8f911684c5a32121b210901631218c570c9690500a0d890c0888904306b9c14060b0509c52684a685064684c8228841498084c602dceec726216d8109407ceacb181aa4e436217523ce8b48da2f51588dc47620b52a3c883885c86e60a212981417159615161213121202f28ad9524911465c92e556a2b50daa1c665a76d8988cb641c2b5a52d11cb15803d43ea0f9a12080c0549484804c645858418a2e4c6a639100a9e44ea83939689c43f286dbd690d4662e35c1690e5802539b982,0x11306130a1356458bc3a3021302170213021302458bc7cd79c9812c15602e1ec044c89c3f80a6a02c45e1ce349c091629302170670e7c48ec2b01170270e5c0960a9b15c7e1e2d82ac05e2ae3eacd409826042e0426043853ef16c05602b31201c1d6b6960a2c5e1d2f2f602a1d340a40188a4c084e8858084c0860084de9c39b0245b41100270f6022604e1c2a5e1f2f0e780ebbb69ab296ab126314220e1a14d90c170c168d941011145010d0140e09ce070d910c09cb860b8a098a090f088e088d889047904691059145114491441203928290029841114118008d00877135895c4b5aa8c09cc0135096b456294c222a202a2228202620d73621718070426,0x802c1da7f011b0245e1f87e1fc0537c05c390023f40bd017902ec05d40b6016802c805480a8814e0580bc05162f0fc3c53e043952302458b162c58b17876fdd14d3f0f602e1fc045c19c3c58b149812297021b02458bc39f06580ac1515afe3eac5b01580a293025808d812ef2f14b8126f1fe0ae1c9830d811f411e423b847608ea11a0232045308a411442270229dab878b1787e1e2f0fc3d809c7e5c99b2c05c3c58b602b0145b011736582898922c58b16c0517c25e22e1ec15dff809fc09e813c827604ea09b0134026404a40944127022c58b162c52604b011f02130213021302452604e1e2f80bc05c39302130245460477d580898138726048b602b0,0x3004c1f29a02458b43d00a2c59010480122c50854a10a4c09162c52404ca972e0f962a58a5809968050028b164058028dd3b0204363aba146c888d144029002c1f87ca8009412aa7c09e2a9055008d8711813005802260c9b162c5b0148092930250e6c084c0864091518109810d0b307e7fc15c3bf803e807b00f401e403b807600ea01b0034006400a60148028806e0258bc3a58a962c50c58a8c0862a96024a1e1e2c58b162a59b83a5e5c80322ed4842990270e40087c0921a264c6e04b0170f83a402400a8053707a0970f162e5460409706580a2c5e1fafab162c00a2f00a8046c09] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc8_ok : checkFCFull 7 [49,82,100,104] [115,119,127,123,117,125,121,118,126,122,108] [1,1,1,1,2,3,3] 12 14 [0xdf405838105a1c2850a162850bec29d0a108da1d1a01c0d0821427b9de8031142d0f14e5418afb858a152862d0e152850a1428603c81c76692ac82030212120a12820241c151a24992618141822151c0c20da76d609882885460b5a83d501c22f283937c93e46731b589a97d55620f11b6a3a654245d50cc83581a4058209304cf342481ad09690d466227105a82b61a3161e229907f3091880d114c0a8b104a9239d7ab0c45625b95989ae49723b9adaa2c42630e9492c27725ae7543ae5b52ea5791f889e54ea7ad09acc3a40b4c730910a0b0a0a118484390d8a41666e45721b51188de42eb1391b894e42e22ad4c480fa83e445a2f5196a0c475a7396582,0x2870a142142850a10a14214a10a10ae1c2850a14b731cc71a34af0a142142850b43c50a1428d0a10a10851a10858a17f007d00f601e803c807700ec01d4039806c00d0019002f00214383838b870a1086284210851a10842972870fa1c21e6142850a15285cb143cb8571c2a54a15fa05e80bc817602ea05cc0b6016802c805480a7002850a142850a14df0a63dd0a142850a578d2dc2850a142850afe04f409e413b027504e609b01340264046209380142850a142850a142850a142d0f162850b14565142c50b162c5a1c285aa1668d2bcb70a162c51a54] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc9_ok : checkFCFull 7 [25,74,100,112] [91,127,123,125,121,110,126,122,116] [2,2,2,3,3,3,4] 19 18 [0x871483066d0d484a51181406055bc29cb4c0a5931100b0ce24b1532d08a51862438221a52c59623b1b56c5a56529292b491a47521a5930ac7513a65d5089a45c1b809904c154d4b1654f297c684c36628f107688c604a829276b4941e312511681a40ab4430a41186110490b080e0301310a0e2c252a2201e101c5ac4b621b10d6b19564a88e18b1858a0c515a2edc928c94c33855e06b134b030a5238ca9456342309a5a92a00c14a50d2125c10c4444821858043169da684812181016141215100b4a3e9308a5a54430110b6c1a485382498241054120e090d088a9148094809058a550b8a8948da4ad618a5946630e10f4aa9594a3a50f889b46d28a5af82,0x2820c84360458b1787e1e2c58a7c09178736042604b01580bc05162c5b01580b878a4c09f2a8b1787b01580898122c526048a8c096022604759558a4c1914b952c0534b810b812c35cbc5aa8131f8ab011302453ea4e1e2c58b602f5f8726048ad3c56de2a01c453c9453657df66240588b14f05c7a52a46a2c53e146bc7cd40188a4c086c086c084c084c084c09602f011b02179a270225260440043ca4268c8b143c3c5e1cf813878a7816207105681b414bd791528982590a09c188c160c13940e880e070d090c940b880b900b084b140a908a904a1188908893081208100694060c060d8509c505050c03148291410e010b01188085a9194b89644280704,0xe001b802d8019009c08b162d809f5560256048b3787e1e293024579eadd3604b0171e4c889c09c3c58b162a302458b162f0fc3c526142e04b09458be02b0158089812c05149813872e04e1ec145c09602bb1787e1e2f0fc3bf813d027904e809c0137026404b6086412302c051629f025e8a2f0fc3c52604560c9b1787b0145e1ec2517c1577ce5602e1e2c58b17878b162f1f15bf8b17c05602e1c9813878a4c49c3d80ac0557878b602e1e2f1efd02f405e40ba017002dc05900ad814a028c0b011302458b602bd1458b162f0f602b01580b87b3d133a45b01458bc3cde1f97b09458b16c05c3930270f17c0556c35162d5b0945e1df411e4238046e08b611,0x1f0270f602b0145b01072e0f6020872842e008296c05943c386c056028b16c058029015809285f01454a18b152d8092af4b4044408962bb6dd2d4f87a5479b55d813078a18a6c08cc4941af01355b162f8092c80a8050028b802e1d3812005c3a30e70fe0a8be0a9b4027f007d00f601e803c807400] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc10_ok : checkFCFull 7 [25,88,98,100] [89,123,127,125,122,126,124,102] [2,2,2,3,3,3,4] 19 50 [0x4858600e09054b4cd2ca5c90d286c3b8998288a160aa24d32a9710c49670120291a023c4300914a20f011007108609451320948099460c8200a5050aa0a0ba7392084b8691521048608c708860829492d0751940eca321470bb3a248521b201614530039401884700e51b4c05051b50943667119c11920a4aa011c0e19444b1a50b2c0866523ed2f6a09629210192805183b0c50b2180c042480b6c32407953c322959495a618c338a111830424694228534d0b61420e9176868434a42dd99882a04258e58c4230908462ea9752c2581634a195218338c01da36d0b4c685a42a1d276c5180e9445a4294470c64882c04868650c41409b44d246d294a28413002,0x8e4f8c0f058384e9a91cc8b080b080306070b338e11cbb1ca51ccd04c6b0ba684848600c950d9885972666648462a322228452021204a0a12b6a43321700a0386420451c4710500e540a520a5108560272cc6cc65ca4243820346297022a11802981544268208ce9242101dd988bb6ca3089308a458856daa5a5391580ac245016100e1e8a0cda665b06929454b6a186a8396d8a52524a94b29a94d4345d50ca26702b115608c034c1ac214d0c02e4228411e4016320a2c0434064806180c748266586c4a50421c340e0e1808540661a0728240623d36402a0aa4dca90e8e02110b09490069881c6828036aa084a0214b5501366536450c5b0195474e59c82c8,0x104e0580ac0543d8088810e8108810e81287b0150f43d80a872e04a1c881118111dd2c0543d0e4408440943d0f60252044604462455d170250e8c088c08abaa1d7812c04a40874b97b97025bf43d82a8f220cb0153f4b912e58097812c048430b62b25234e58088a91016287001411f113e11021d2a51f602a7ce812c054bdce5c2943a01c5f4a87a1cbbb2c04459973d0ea4f874088c985c0960ab1550f6022e14afd2d4e813143dcf43970250f6c2a1c89108850e8d12d82ac144408803000e83be52742314b2950f439d0650ebbb67109b210f1c06160322012e5b109f221321051a01240516012e43622060b1101950093008c8099a91da392238d138b13,0x2474084408742844087479602a1c881287a1ec154f911253e44094397022f0250e74087408440844096022e0cb012f063f00bd016602c805880ac012e050f439102580a876bd42204a1d185297a7eafb595808e81287a1e87b09110a1702172a110652f602a1e9f3a04a1c8810b8f287a1ec054bd6f439102170250f479d06112252f602a3e87b01110e170250f43d84a8722043a04a1c881088108812c05612a1d7831f809ec13d026404b2096010c82360580ac0560259150f43d6f6022e5ca1e87a1d1810881287a1e87bfe97b1d11021d02580a87b0957f43d0f4bd1f47910e291658091870b810881287b153f883e907c20f641e8833106420c4416482c,0x4b0087410c823e01102580a87b015808e81287b011702002e0879aa5a5e972814b1e872204b1150ea8a3a044beaf2e64b055808e832b7b11140255f622a1cb83119128f220c520c34043a0446244bec144458443943d80ac045059c0a809700901608812873a045fd260250e44086809040943910250f43d0e5326b6b2a5ec7a7e06543d0f60aa3ec3543d82a8fa1cb8d1e9d0251e500947d8e948d28f46046404a1c8810e890a012873a044afd08f811e8232046208b2116020c843e050f43d80a87a1e87b01350250f43d0f7f2a1e8fa1d7872bf520446aca604a1ec047418741943d0e440943a30259aa0810e81297b01582a97a1c8812876a4ca5e8fa7ec,0x943d80a87a1f80543d0e002828634042e0422044a5c0846a943d80a87a5e8f3a046a24a7e9fabec0543d7f4bd808e812cb444089500108810883200547a30258f479a02230a1d0223062f02584a87b0511021702170a5808b8110012c144409002a1c883088126810d012875bc3d1f602a1c8851026153543d2f5b911641290010e912d7400c80957f63240385b550ea8ab115ae4408740963acf61222443a04b0158092c868b8328f7f007d00f801ec03d006600b2016000c804604008d012c0543970250e9687001413f52eb42a1d2f34acb1124f61255d700ac0547d8f47a4e4408f52a30217021d021a2225805580b81547d0e4418fb04f4097412e02590,0xc0547d828e812b758955e4458743953d988e81088128fb515808e8308852c4547910650e446960a2234b09704aa72214b011702584a004440844094fd0f43d3e44285c18823000282ee5e52ca96d44408afddfd3d1f43b7412e025904b0087410c822e050e128044b202085a1e8700141531102480b405802a1e805602bbdd357391021402586bc044a23a042204e5ce81090128b4ad2d028881127a1d1d3e4438440943cd5204a3ce81118108811087329702500b41474098bf82ac0560222040d0e44089488126832c05402db43d0f17414741880b15fd6f5fd8688a915b44438b2253de9a4224f57b5221c2204a1db2116020c8416029021102700ac04440,0x6d2e441947d829b2116020c8416050e8c0943800a0cda872204a1ec0543dbf4bd0f60a2314a5ec055797161d022f061102590ab7221c220c46242204a7ec34bc8947d8894830e852873a4c3a044604220ca1e9fb0951e5c584409439702580a87221c220c4b47910e50e813143d0e002834e56951eac2a1ef7b395b8ac255fd3f6022e5c8011d0250f6022214a3ce852c0543d1f622a5e68108850a0122722043a04b013980b20162022c080125a1d2a52204a1cd01000e061c44094b9d1251f6022354a3ca012c44a822e042e2ca5d69a06586ac154791221a0650e4439c4a2224b7e87a5c8912c7444494b9102582a8773086410c42058143d0f43800a0bfa,0x2872204a1e87a1c017075d602a3eaf2b950f602a7e87b0153e453900a4b4bd80ad2547970e57f61ab1ec25602a1ec7b0556f43d96ac1543a56e825c04b2096010e8219045c02e04a1c00b06ed43d0f43d8495d553dacac656c2b0d2f322a094852c1557d80ac0474288c0874394b910258c88872c4444196024b60a4b602b015889016287a1ec040028536b09110e53ea9a22042204b05580889d2bf2204a1e87b2d58ea97221cb0959f652a1d] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc11_ok : checkFCFull 7 [13,22,104,112] [31,127,109,125,126,118,120] [1,1,2,2,2,2,2] 12 22 [0x157c7336eb3c62121e201a3812141115901109290821d28e9172c924292402a414a089a3249518c5108c8444644660804044303d496a7b4aa6122ee265282807188389693b4a99714521a530840d52669c12a697c423e1e8ee87693b05d2ce8e74332a4993085951180252c9d60eaa858ba8a1910c4302430252245203210610a1196bba984158f100e880d080c90070887148490dd480e08a202a41285214610e11a445299d854a1a44ca415248c0a443bc251b483a683b061c01cd94c07509a2019054284140e95a45522a50f2a1844428dda2ec3648aa4d548ce08c039509805d302129485a5442329840939613a8e120e89a65431010d2849513a8019282,0x17f007d00f001d8038006d003e00d80952e80a2852852e54a952c5cb17284e9410c50a50c5e1c3162cd9bc3c58e00ac54b52c569e6d00821e1f8749d274d5a0176f16abf40bc017602e005b40b4011f026c08b162d808ed5162c58b162c57be2c58b162b9f35d7ab16c05562d57f027804ec09c01368268043e08d81162c58b162c58b162c58b162c58a7228b162d80ac05c3f0fc3faf162f0f17878b16acd6bda773e2a02c458a7328b162ba4a2c5e1e6ad56d7878b17870b54b9500e229d09d55143c3a5e7cbf4b13a00c70f162c579170eec28b1787a1e47e1f870a51d28911488b0814858c848444890410e1806c42644a402424a220d4388c20c4180328,0x22c5e1e2c58bc3800e097a6d59bc7cd8a6ea8b16c14dbb8edbb9efa02f005d80b9017002d405a009b022c58b14003047d362cde7daf8b75af8adbf5ef3c58b578fe5eac5ab162c5bbc3a01c458a001821e6fc1d4d39aa8a76dc6be0138026d04d00878117c0416405142862850852f0e1475543c58b16296e942ecd14966ad8bc3c58b16870ad3c5f0105adf87ab2028bc3d5e1d016229f2a2938a2c5e1da7345554b362c569f87ca] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc12_ok : checkFCFull 7 [13,28,98,112] [29,127,125,111,126,124,114] [2,2,3,3,4,3,3] 20 100 [0x581114140419044520252074e42920130850241e3a313e21261a0261084848621c2804618831045104311440342d244462202614261ca7551083b0098a08904c110899009a008f4f8a099d889442106582a04ce867746118a8183b91d92408640904c88cb10c26200402482273144d3e500c2124501443848d318809080443112182e868704c2843a31892192ca38651010961543e3981298038805851299a54b2801e3a8803c112a01c21340a86443cf31225884c070c56464aca1c234880c12878941d321d95089961ba1e5425042602b489a630291d430a564c4ac21174e07693aa0909254d0c2045522e511486a614288183087a553a8a10b285a414a02,0x438b4189e13848e060c0b0cd4f2d472ca72c62b204d3c1d1c6458501c61970a428132947219b22121212151019030c832301151114912012315332520898044f860023698f4c68610962530191c0cca4b52365ed0f87713a49522ac435d032c8229063d23169f382428c8168f219814871a113c0112112807281e281f289d080b39942692233b8ec13030565a008ec048a4852488840a80446ea52212020c8688b0a4b4a50115c8208c48944882902329da4a52221808d50415044a22403c6110687781424123894180b103a80e0d008a01940192080a050d090847060189c809019882144305809248880d1919580898082210484c432c450608682aa81c34c,0x811787e1e2c5e1e2f0fc3f80b877ad780b878b70a8b16c046da8b37ce5162bb2bcf6fe6fbfebc5b05456be6d5e3e2f4f1510622ba28624e39c09a78b612b0174e813114dd46821695a09a7e3f87bb566b5fcfad9b18ad7f2f179740583ed70eebf9f17bf69fb7e1e2c5bb15a7e1d3162bd8b76c25562d80900e3f7f1d76f149930700308d8963d8aac75642f01584ac056125cc10940594818c9508cd8c15094910068c0194009201926ce658280cb0088d2f22c620c403a5486120c500876461a26320c300c64c67088725626242820380470c84334432c60184085099340c0c0a308918870807190115c2e0092cc92cc080c12491345900590050e019c2408,0xd6de878b14aa4fcbe82ac54962b8ef52771c2fd40f8807500e200d40407c80f100f3e058097456029b1f051baa2c546e92e1f876fe2cdf392df5fa77bc3b4fc7d84a2f2e73c57ad7b6e90b16c1583d50a78fcab66f8082a5b01454a20c051d145291134a2b8ffbfb8a1410560a2bec24d3b3e3fc4455479b83d54a9f014da1daad7e027004de087410e020d045c01d51c89af355058afbf0f162c58bc79cf162b7f146b8e16e930245e1f87abcfd4fe028b14a7e1f873bcb85b050de7cbf8b362bf823e847c08e411c02378462083a10f8072236d45e1e2bff162ba09c78bc3b8f15afe1e2b6fd7c5edf8777fdf8b166bf903ea07c40e481bd00ea01c401a80f,0xc5e1eef0fc3c5b09459bcff1f362f0e37a7b0145f055d48183d570e72a6bcd8516ebffe8a75d580ac54ef9a4ac04e7d84bc3560a8b602f013f01380262043a08701068202026c08a72a9ad7db69f76dff7e1e2c5e9eab8f76ed80b9fabcfd5e1fefbb15af77dfc11f0239847208e211c02318462087c0e1f878a4f49162baef0a8bc3d9aa2bef56abaaa2f969a734945e7f97aad3f0fc3cd69fa7b0558abc25c3d58be0240983a51ae9bfb154d8b17a79b16e9706458b56c1517878b5797e7da7e3e2f2f36c05c3d82b9f40588a6ca351458a7822ec469eed90a2b6f6127e017202e005bc0b1011c021a04d8095755118506eab5de2baaa974abbc8ed3f0e939,0x6ac3565ab5d580ac3560ab5cb8d28f3a04221c221cb0957f4bd8ea8fb01170a580a875e0422042e0c2e14b05204c598ac74440845e96eaa9ec745c08ec394b910e54e5c285c09602b05170a110e582ac0560246048012302110e58c918920049030b9a2e542e4cb1d111617022f0253ea4085c19602b1158097872c25c2ab094d0615b01580ac05602340440380bfc01f403e007200e001bc031001d003800340270387f0170fc3f0f162be0a2d8a9af77558a8f04e3b8e6ba9b766f7f602e3e2ddf5eab4fd7f0f162b5f362bf200e40403e807900ea00f401a800cf8078a8b162f0fcff1fc78ba82852dda77494575fcffff97e1f876fe2d5e5e2b8ed3b4ed7,0x728142e0cb05172e52f61ab01580b815612b1914065828a012a7805140240299a8080e901c201a3c04604be5580aea45d39612b0d5808b810a0d2c9501ab3d2d2e04b055808881207562aa5c8870b852c345d08745960a221cb0140aac048c19602b01140223064028a0b2c045029612801220c5d095656324b77d8293f2e3cb0d40c8d0d2c945c0964a4604b01592a972e3cb1925b31700ac049791022db095829807500e200d160580888117957423a1ca1ef7224cb05586ac0563a220cb9ec0562aade872e2ca7ec244418a53953d80a87adec156222e042e242214a3ec056222244b0117065809e411c023104160580800b04dc8d39602b2158aacd54bd9,0xb850b8b287a9e8fb09171a170e1702580ac0444385c2961ab0152e5c9844895fd8c91872c05612601d403880345808fd9602b01580ac045e8947d84ac045c5960ab3d175258a88a928f2e042e44220c4604b15170e58eacfb29171a110254f5ba30611062f0658097812c345c0890300118206b115c2ac045c0845f96daa1d50547d92ba7b252f0a17025808b83118f0b832414bc0943d8cac045c48740947a302171a580ac14ec094bf5e8c088c088230005850ea5e875714a8889518872d2547970e58c8b8d1e405c00b101160140258092f008a7b2d4508a2804b011112700b855612e05143651ea479c22400cb35580a00496c045c1903a8195808b9316,0xd90ac94441961a545130e588ad745c09662a7cb932d72e2c90134fa0ab01170251f6122fcb872c848c185c2943970e2302488a9f2644b0158aac3562a260c9b16424f308e411c4238046a08c6118821b024056028a7c09142f8088810afb3c65202b8d1902059055809a7b190aa86f8282d909c790d50f4bc92898517832c644c2960ab054808b812c75e12b0159491810c870b811781287b1511061502684ac348c085c184c29e0a4a0c261c2a0c91115022502204c50f36a3c559ea8a0a539aaabfa7ec056728a5cc94f970a171a3106052af310e421c4438086310c420b80440943d8097b44409439d162f8e17021d02580adfb51171250f602b415848b9d,0x50f548872c3547d82a8fb09110a1102580a6bc8238046208080878143c80a2d80a2800809fb9778116eef9a4b7754952f17bbe96dfd1f296cfc3f0154bf6f172d8cb878b87d8f47f2f43ed4fe2a80f901e203a4070807900d2e025a1c00204dc96bf5852d087804a7acaac049fab8393d5b4bd7f43a8e4429602541406aa7ab53d5b011d0650e4409d68fa7e972e04cbc3d80a879a883097ac68bcb2ffadc645632541110253f622b092580d5bf4ba68fa3ce870d053c04d3a04c6500101472cf652b05410ad347c7814b8729fb0553e5c096022224a5c29702201c0016123a8756100160a3ae8458e821c041a085808c09602a1ce81287a1ec0543801608f8a,0x1417751f77ab3d5ff6bd5f77aef03a2234a7ebf5b57d2e44785c0965aabcb83287a1e872204a1ea7a3ec0561ab0125b0958290460005072d6b25d95af60a87556e44490aab3952f43d0f47d84a87b0953e5c394bd0f6024098002c14b2ce44c844c844b943d9ca872224b0d50f622b015808a03287a5d106287001419f3c80b80162022c0b0150e00582b6b012a89564b425b9590aaf56153f4bd8888812cfbde87b3d807d00f201d4038803d006970287001419b000a085ac1561a5752a48e932c2444595bd4f73970e170650f60aa7eafa3ec73a0cabd206287001414f580aea54f8425563d2f672b0d582a87afe8f6aa9aa5d2d80abf523cb255809a7b05,0xb5ec554b972652e445960a22acb0153e5c0960a2224223cb0153f60a220cb011106170252f47a40c50f43800a0c995956aa5452a8a87bfeefb4d580ac85662b0550e442960ab0553f4bd82affb05586ac5543d848e83148108872c256023a04501f203c407480e100f201a4004d81602a1e87002c18758096c45c0943d88ac64adab0958aa9fb4d582888d2c1501aa5ec0444984458444943910a51f53dcf43d4f4bd848b812c34441953d1f602b01230650f6025b61a79847208e211c02318462085c04b002a1e874a00282f6551584929269ed8aa977b0aaa3eaf551412a9fa7ec05662afd5157bd3f6a2a9e87b055809e621c8438887010c6218841702870,0xb011102000a0cfa87a9ea7004413f5daac2568ab05586ac655bd0f43dbe441943d98a87b393016a01f403c807500e200f401a6c0be12a2ad14a82] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc13_ok : checkFCFull 7 [56,73,82,100] [121,123,127,125,122,126,124,91,109,118] [1,1,1,2,2,2,3] 12 10 [0x58a142850b162858a142d0f43850a14624142850a1428d0a3429d0a542a04c05195050bc3858b57b4e8031142858b162858a162c537d058a142858a142858a1826212990e0a6c880a0887088608c283414680cad68e764460b0d155a72d2568ab4c83824101894b57da98d4aea37519a8bd43ea0b1a76b4b585a92d33691b43da9e939497a49d24691f4c5961cb065212c67623aa1948c92644b22115869a154828f164144b4d0a50ea83111885c516a87105490d535a82d82c482c080c0868880608a5452182fa93d47ea3b511a83d53da42dc148ba43d20692b2c2540dc436216d076c0a43534e91d883c41228ad15aa3b612808ea0712d486b466252d6082,0x2850a142850a142850a3da0a142850a142858a142c58a162858b43850a162850a638d9a142c50afe00fa01f003d807a00f201d8036805b007001380142850b43851d1050a142850a142c50a162c50b142c5a1c297e54e85aa146bf023d047908ec11b422d8452089210e0223002850b162c50b162c50b43858b142850a1428] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma fc14_ok : checkFCFull 7 [13,50,84,104] [63,127,93,125,109,118,126,122,124] [1,1,2,2,2,2,2] 12 9 [0x2b0160f602b01500b0048c08bc096028bc3d80918132e5240446042e042e042e04b0117022ec34430588989ab6453065292e08603b8a29092983167893c745b2ad4d6a4b44db869894a3a5152629254d19644aca55529994aca36186e9974c324d5b88a844a22211806c024b12421294d2a40da05dd9a8c354b544a52080c460b068a086945090525442504050944c2c20a38e0b49db0290d4c494c4a0e522e864503a0a5150eca5942221a124911823890c436213107882c495a2ed076a9a475232913487a614ac65612e0a261a0608a62882a4c434842322130202a09c60da96d41685b6ad2229512a094d4a891a1281f8a1b455a22d834a3949ca4896e82,0x3f007d00f801e803b006d00ba00fc01f002850a142850a14001041c11a0aa0a142c50a14a85aa14ad0e8c2142857e017a02ec05b40b4015d02a804fc09f002854a142942162850c50b43850a10b83850842c50850862850b9528baa2d2e0a20bb0ad687c5c295a1c2851a01c450a2d20a14314284285a1e2d0fc3c50a162c50a162858b1429a882162c58a942850a18018200454042404cb96c05142480810e5ca480983d80b2d00b2d80ac05602b0165cb9bd80ac0478085c084008a8085c0878096022e042404c1ec045c0840085c085c09c396020707b01580ac0458096] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r1_ok : checkRowFull 5 [7,11,23] [15,31] [24,24,18,18,12] 2 55 [(0,1)] (forbUpTo 14) (RowSpec.simpleNeg3 53 (-36:Int) 55) [([0x7040c90063],[(2,(53:Int),2,[0x8a1830c2])]),([0xa495084086c1032501984814c0450215301284c14804b],[(0,(0:Int),2,[0x28421421c1c9013294024509002500a8051437246245247226225224a252318e1b26a63c587060082])]),([0x204652104325c10ca620844b8084194c90930080b29921250465321022204ca620432099484086f],[(0,(0:Int),14,[0x254a9500110010d010a2920054fc02b80495ad0f00a0ab80f00e0254004348c801400a87a1d6c0aa00494285b90b20e416040092a5a1e00418012526544a9be06b6ab40e80e0252e0480160082dba58b1780501aa1e8f0a230aba54a444884c354a430bf850dc91889050d97263d26058331471249020a4a318992548e9280c4cd1342d1262929230630522c18939125124d634ad1a691c368a28922da441b82])]),([0x1],[(1,(0:Int),10,[0x250c5c1cc011515c0a9a1a1507975641c81c08b14efc3f015108544042004ab14b011098c618bc384bf4a555c0780702285ca17070a94b8109013870a7859972872c5f0d05c012430142152f0e1a9239120a10508224131125130520329118a22918618529114431c364d8b48d930c180b6092062481063822821691268928122c28a10d1682]),(2,(-36:Int),2,[0x1c3f0e94c81307b01500b07a1f2e58a968054028a1cb002901069308b0c2c82ca28a24418414d1091089049041080cc08208e04c0440410404ae03c05807012])]),([0x1],[(0,(0:Int),14,[0x65229480125c0175ab402a092dcc5504060049451469dc5e01587a51180c6fa7f80828090105f69707ca1780453900205801072c509806565ab701e02c0380781972e5b01480b874a1d011b02120278e14a942f1fc3846f0f950180ba020a190508230414418a20610104130a286185211244514b44d0b50922441c18604418828814888408904c049308b0c08c368a25128828228920da041882])]),([0x1],[(0,(0:Int),2,[0x12c0092a54a96005002a1d2d80b8049529d02110214021402110206c50a44a28c24418414910608c04844510c411c360d2340d424090382])]),([0x1],[(0,(0:Int),2,[0x50e10842c00b070d00a2a2021e0216021802042869448a8924418c08a08608288c04a040460d4348d424090082])]),([0x1],[(0,(55:Int),6,[0x60f972a577f014dc0780b00e01e0500b005802cb972960216020520041b83a031e028a1a88248228282182291844319362d6350d2342d124298370d0282])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r2_ok : checkRowFull 6 [7,57,58,60] [63,59,61,62] [24,24,24,10,10,10] 2 57 [(0,1),(1,2),(3,4),(4,5)] (forbUpTo 15) (RowSpec.lemma36 23 (-40:Int) 45 57) [([0x1],[(2,(23:Int),2,[0xa142d00a805802a01500b005402a0158083699165438d1a0e643988e583950e5238e0e3438c8e642])]),([0xe185148d911dc30528a31a38c258c804867],[(0,(0:Int),6,[0x80140082c5a1e87a1e2810d010a812281129102500a805402801580b405a02d016008b810c37202454286c09c027e61eb0ed80ec0f022d0e8c08540854085409802c1e8722042a042a040a10aa40914e013070a1548134044008780844084418440844192028093426c36398c45e1f878b6022204e1f00543d80876991a6245092141850612144984498d95144435310e3438c8d3244a11223030c0a3019244b0e85214488a2e45a8b311a21c64888542c8d519210c18e7a4f51c9990f3e57aa951163c3782d319122444d228c618a91cb11289912b82])]),([0x144081a2bb23a481024576474502028aec8e86040115d91d03081aa3b23a05102547647409202a8ec8e81140151d91d820429a3b2394408234764724810268ec8e450200d1d91d42042a1bb2390308243764720510286ec8e4092010dd91d4100a81bb2398201403764718402406ec8e2880440dd91d02043b2a1a0604047654240a0408ec864811017620121840bb08110c26],[(0,(0:Int),21,[0x20aa408a469e0ad0525f01740b9043823c08016008293022502050a1640520290145b01172e1102110248089813c4543f7e1a1fc04440844089a3fc1583a116086381c1de64092022804f0160f4022dcb810b810d8b0a812c35c3a11a0d864306c896025a2cd0113020428e08a07a06a05a04a03a02a01a4c79018921275c00afddb766bd5a71640310148cf9b2e44c215048c0814a4c21282032c2850a2a242062ca8b292244305300ce332244290a24155a13142619c2a34458871a1ac258299d9232125548614491038328089026030e45a89849c34c8931d22512151462a4728e317191c68699188d11911198e11aa34c74c886364528c51d3132c45482,0x1001090109010901100109010901090115013f5517f525134f162a3c08174078b032a5b01200212021202120220021202120212021b9a506a5f811400a005162b5f002805780a015a1248319400404cc19720390215f907a83c41da0e9072807413810409040894088e084c48e408e4092029051102112a58ca8ff0170f40a222447041806809178790125d01480888128755d400912560a4bc024b0409040942a260c1b8020a116086381c4ac88b9098102c809ae80888112fc43d21e10ec874439203906c00a17879014808515a029014809c811c81240520291561e9717e1e870ba])]),([0x1],[(1,(0:Int),21,[0x816060f83c586960e17c05162858be028a952c088f0708051aa5a1d2e009b7d01050e54431879e021e0e103225f94285483f887a43c21d90e887240720d809629402100248083a024a9529a021802700a404942d80895514f010f010f01021f011002458b9fe5a1fc049421e01250e0ea0d9098e23018908852244468c19089120a246992484b2a194848c140470f2a30a4c12206a24c4489912a3a4528943048a71d0ba0f78c9390f20e7aaf1584c228488c144844a113084a224488409100a390832206020316810c2884402048893408284308d116235464889228c74c471a198e58965210304061028a1428495526518941c48d3221508638c698d914482,0x116804962907a48091c84aa901e50ee3a52ab4b5d1134028013008704780162aba92e0fc3bae93f0c068257a116086381c60e4ca4aac2cbd2a54a95ab5a1d5b3a01d0207902083a3c080f4041f015e2ed7b2ea97905050e55c04d025012408c04502045702301140880430210102358108082040e20068183a556560e9687e1faf84a2e5c1e6c581556e172a5c1d285494f01a413054a474081e40]),(2,(-40:Int),10,[0x83b00e801560458b17078a10e0f952c590110022564d353b60a0a53c043c043c0c3c04da951011ae0082168fa01654830c8aa1e2854a94343872c5a1cd3480e1f070aa00916284394285ca10b83e0f8cf010f010f01129e02500928540040a943802c1c38386285422c10c7038ca10d2224221224542148840190a8621190238086022e40508122148e3420c882460e042810102483918e423840a48085024e411424eb900e28889223838d0e6589654594955265218c8491124238d1a0428089083409908225120424091025809888540940e303840e426180e2851112583880e103080a2848912683990e323880c22608061ddf00f407803b01d00e400e01e,0x9707c1d2c50bc3e00a2e0ed0a4859b0020ed4bfad8692c4ed59c82e4081c42b3a08502039004])]),([0x1],[(0,(0:Int),18,[0xd105039ca940943e02ac05942e50b9529c02458a9729c021c022116182c0a8abf7e01e80f007603a01c801c0360250ba882a0024009285255001200543c0cb874610bf10f487843b21d10e480e41b0307c1c210c5300430048b4385cbc02a01102e2debe21c84218a836426388c45c1f80513d0f972d0f1769b02458b1629b021b0220180d50822210843810a14463880a64204066811204480914675c9cf2230aa924848a11c6444c14248053404889081488122445121818a05300c27a1741e9592722649a9912a3c1488c4a12242e78a02142104510830220188032488852048e514225022448a044888d4598c2a0e46c8980984698d51d238c588d113b82,0x1168f5cd9c8464172099020710188567411a0407201907601d006dc00d0fc02cb16870e50c580150f4ea4814bb03a4804e1f82596ae54a70099628729c021c0224182b67fee8408114700218a10854a14211492502042c5a3])]),([0x1],[(0,(0:Int),6,[0x143d0f43843202375486a404fc03d01e00ec074039003806c00b402a1f00583d80b0056024b9707801130222082c00a4148060d01129a02254a6808952a202254a9510112a202050a14210d244490914224485122420884226050845d87a6742ec992720e78ac554aa0c784e11aa2c4748e31a22e4598a11ca364698c116a244542848c111050209101982]),(2,(45:Int),6,[0x58a952a5c1c24f2cb47b3905c8103885674080e41d8073e02534044a9529a022402054a952a54a680916874b002c016009101307971520c0421a0150e16878b96870d10848096425508a224250604440988e6038e0e3438c8e303880e2e41a0e643960e543948e50388882810894483910e423840e2808902081020204084842260488180920424205080cdf00f407803b01d00e400e01e])]),([0x1],[(0,(57:Int),9,[0xa01051010a1488088809162d0f942a58b402801057e01e80f007603a01c801c036022022202458b43a58b83c5a010d7e21e90f087643a21c901c8360500bc05002a0105a01480ac0596405402801400a005002a01058012b2a804a0d9098e2300c180204210a10842980218020438c3221060411124404883193b1751e93d13a1741ef998728e42cf1552a954aa951e1384698b51aa324748b31c62a4588d11ca2e46c8c114232444909142246091218489081420a041912182])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r3_ok : checkRowFull 6 [7,15,23,56] [63,31] [6,6,6,9,9,6] 1 24 [(0,1),(1,2),(3,4)] (forbUpTo 16) (RowSpec.lemma36 6 (-15:Int) 15 24) [([0x98d40841d29a89003a335210072c680420e54d04801c99a108038e43021071a862400e2d0c8401d3],[(2,(6:Int),2,[0x254a952a54b43d0f43a54a952a54a1b8d0e3238c4e2c38a8e29233e6cb931e2c3837c2])]),([0x894654123026c2a32a011893614995004c89b122ca820644d88c653124026c26329812093612994c05089b112ca620844d8984365121c2c21b2810e2498550c870a2c0a864388a6153421c24b029a10e4899484086c186c84a42c184653200c6c0420e14d84801c19b10803812],[(0,(0:Int),9,[0x70fc3f0fc3e5e1f877b53c445e21f10788781c3f0fc3f0f97874993c425e11f0878478010e0f9421707c1e878b17870f0e142104d0521c8b016804162e5ca1084285a01043402ca10850a180e802bf66bd39f2e02a01aedbab466cc28288889849562aa552a935c232454895126343646a4d4c796a8e36a3b66ac751cb5526988754ba96b2a32c40d2d74c8b2913aab52582])]),([0x3080140576475100260aec8e92004815d91d1400882bb23a8201503764730402806ec8e3080480dd91c5100881bb23a04414507647404826a0ec8e848054c1d91c8900a183b23881412307647080bb10090c205d840887020eca86438087653421a043b21a90c0a],[(0,(0:Int),25,[0x28575d2c008214264081084504152b5e346859b578f1a97820b901c81600514970e142c50bc385e1f8f6aae285e1ec4453859af42a426188c680b1850a142d0f60290147878ad52906116086381c13021302049813ce4ae2d0f9628e01a00afdda7465ab49e4c709126ecd7ab3e6cba13c857245890e2934e4c2530c5734044d90258087aa04894223080b34c8c23112446302a409901a4890a146513aac2a30b13240f1b21168b008a12444838b40b054603889309824608d6ca40d6544a8909429144a214c91128a94d1db95528a8dc232a46a875aa905ac954eb12225586aad58899136b1a217544c228935a1ba6230a121244d2ab0a44b59ab0a84755d82,0xc1f07901480b072b515c016009298a979a2b3176552c58a1ca1788102e80f403a004980108707c1e2e0f83c80b0768d4bf8a2cc7293858d50bc102010e0054a1086283686acf18a931e4152120c5e8f6954a908d484c311808348b714965ee8a6dd20c780821f01062a4d56d6a50dc027c12e08f043824c0c1f070a092c7ea77be49587ad69d2f56142bc440c00b14de51c8d73f9f90915c3c35687a9d22c050a779902190205a1ca74bb0bf7c02a2b9ef628d0af1017807c01e01e0450850a14])]),([0x81030ec4208f810221d950d1e5],[(1,(0:Int),21,[0x249399e845860b102282d2d0dc405e01f0078078143d80a872284a9e97b3550f47d0f602a7c2be02e817008117c09c0408de043e21710788ac03a04a1df7a1e2d0f17cf29ead0f4fc069e013e097047823c04a96c0494f74a9687a1e872204a7d474a969fe1d0430c0e08810881287a1e872204a1ebf80150f47a099062c0543d0f6cab3e28e12b4484911a0261218c45911128448891c24505084891c945129c6230a14a4408941221151b15664088c181020402af5c9ca82488a144354ea83708c2922b437ce484c036108a1279d10a4225111242d30a0eac916228c4888ed1aa1d522452b1d45aa0611450288541130601244448c102492b2d66ac4d3b82,0x680a870850b1687a1c28420da4a16c05346c554d26aa54bd02e01022f012008f845c21e11f02874a4c2a1d2d82895414a95377804f825c11e08f02004152e54b9414555e851a10d809374a5e96004d501c444a]),(2,(-15:Int),22,[0x6ab3a1f2b5343cd0c00a0050024130ede0140087012a54a49a4de978154048294e960050028012116086381c06484c0ba03d00e2c0a1d2d0e952a54ab3a54b43f0896a553d2d0ef42f40b80408bc043c0a1e874b73a54a952c0a92f4dc2f0083022852bdf142c009474b95274070952a54fd2c04908b0c16287a1d514954780170e906035128898611944649090a8429899222489107211c044408902285184c30a1c18428112e62104844891c982459190488881a4a406027088c227051e12507911e60b92143011c48225039420e4a2424509211ce211024907213040a3848e22275ce2630940cc027129c282061c467019c0c7028657001f00b803c00e016,0x1439c6a9fe011575f69546f813909c0408de447022110d8196878a14314218b002801230839])]),([0x1],[(0,(0:Int),13,[0x217021d0214021a021736782a9fa3de0106050e7408640943e80829f0250e540926a2e3c9012302588aa7a0551f002a1ce83287422c10c7038bdd78128f5e0c2e045e0cb0125e1e87b01252e0c5e042e045dc007c02e00f00781a02d01050b16285085ca6ba42b5e35e013e097047823c04b43872e50b17ef8bf619d5a1508b0431c0e0187dc2f0e10f0e18bc384e842e50bc3a50c81042d8d014249483404c012a04a0114044810c042812240e0938c4e2a3c48612214044c3828488214842311823526ac44a891142b2200950aaa102241e7275c9ca44489c984848c0242612363a8d590824480eb09040916b1366aa06081440d88825ad0d894208e113182,0x58097812c0496005002a1ec0543d0f43d0e49a8015302530214061702170])]),([0x1],[(0,(0:Int),2,[0xa142842962c58bc3c58b14285d016808a81340454085409202901780b4046c09c3e80a2d80b87a1c2c58b2021d84c612984642a10a42890a2224890a0426081420485126038c080d516a2543a85506a05628c1122204686c8d89abb50690d11a13416c091482]),(2,(15:Int),6,[0x600a2c00a2c50e54a14210b0920a946f0083002e0e10c50a15674c50842a116086381c480821c1c317074b17070a9421528421437021c0479c9c48711122e42b9c246088c2224890907211e747108c242891c227850910483901e7131c467031c4a5079c0640b881270288142841220706112e484081860b82f7001f00b803c00e016])]),([0x1],[(0,(24:Int),6,[0x4214a9497543d0f43bc007c02e00f00780952a54a952d0e952d0f002a1d6f403143d0f43d0f43d0f43a5a1d2d0f43d0e19448511124440c102840914aa5546a654aa93522a4442883141a234268d50eb03648c098622d686c4dc222541a8551082])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r4_ok : checkRowFull 5 [7,25] [31] [11,7,7,7,7] 1 23 [(1,2),(3,4)] (forbUpTo 17) (RowSpec.lemma37 (-3:Int) (-6:Int) 3 2 18) [([0x1c4320101e90c4080762140301b884c10069],[(2,(-3:Int),2,[0x2850a1431e2c383242])]),([0x58c80a424ec1885410c885],[(0,(0:Int),2,[0x4210a50b43f0e172c5a1e2a50a50dc71429219a9c4d2652c91cd162aa54a9547060082])]),([0x404ca280464a409944c09094413290810c416510221c10ca8604340594c1086d],[(0,(0:Int),10,[0x250850a1d01680b405b7a54b4bd1ee44388380942952a5d01332a14347b940e80e0254b43c52a94ea5505864612ed0a20c30b19785286a14a4494490c50c5c98f16a2a92206454aa38346472c59042ce0c4952aa594aa593490d82])]),([0x1040010dd95204100085d95210080d01d952080810c1d95202080841d9520b],[(1,(0:Int),6,[0x2e040b9640418a10c50b143af858b4bf57221c41c00c50c50b43d0e1b0145fb15685901220c30b0142e50a40091787d010e24c1851448e40c40a6045044443042444254b8a14894614288198994b25529532c0650260c48221512c09051082]),(2,(-6:Int),6,[0x48082d8082c50a162c53204226ca5dc88181002a01450c58b1787a7f8f0a1510618588b602e1ec0416405e021c9a881471062433022822221220f06cc8ca8c8c92889c49ca042c3b2532c33410724730620702ec80700a])]),([0x1],[(0,(0:Int),14,[0x50920829bd8286b9410720c410811300282082edfb4ba82c32302c20ae48208380142858a6384210d828296c058ba13010493910e20e0072e5086a7b0125085b0170e142a20c30b095286a30930a2860890c918c08518a0890464a444446464a553154a8154314124aa542d0264a5260a09604c180f82])]),([0x1],[(0,(0:Int),2,[0x850a14a14296805402c1e8054028a14362861849860c50c4822822a4922904c150a1502fc2]),(2,(3:Int),2,[0x2142850a9680416805168052020d9a1991961951251439038c388398319219119c80700a])]),([0x1],[(0,(0:Int),2,[0x254a142952a5901400b8790106286c18a0440410494b255249148260a9542ec2]),(2,(2:Int),2,[0xa152a50864052024b2020d9a19919619514392390388398319215c80700a])]),([0x1],[(0,(18:Int),2,[0x10a142842c00a005972c00a0054020d9614398312964aa492290c8260a8502ec2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r5_ok : checkRowFull 6 [7,57,58] [63,59] [6,6,4,4,4,4] 1 17 [(0,1),(3,4),(4,5)] (forbUpTo 18) (RowSpec.simpleNeg3 0 (-2:Int) 6) [([0x68a820411c950804238aa108046c5310208d4a640211a54c84022e21881045a4320108b28642011e084150c215],[(2,(0:Int),2,[0xa14a14a10854a143952a5ca952e54a97286ea63994e55234ce8e3934987251c5870d1c2c727467cd97263c587060582])]),([0x91944082313290084616521008a8c8204114990804228b2108044c631020894c640211258c840233],[(0,(0:Int),2,[0x50a142850b43858a14285e1c2858a14285a1c2850a162f0f43d0fc3d0f43f0f43c50d962595140a3828c863111a21c746d0d69a2b704d89a5342664ca9712c2564aa93926a782c67cd97263c587061282])]),([0x18510042ec69030920481d8d21820429a3b2394408234764724810268ec8e450200d1d91d42042a1bb2390308243764720510286ec8e4092010dd91d02043b2a1a042762010882ec4201111d840823d],[(0,(0:Int),26,[0x858a15dd463c80b872de4055bd3ef4639303982c00f0e14285a1e870a1428a6aa97e5fc8082d4fc385a1d51330b1c6628734905a1cc733c28529d30c0a88c70a14a8134b5c3a826416388c110211ae0e4031a64e2418386062f569d19f365c98f609a431320d052a849211438dd9946b8d12474c89091238e2c152098816202030c6989e34305490a1c24c251c44c833098a0624445091c18a05263094c163054c228b5149b344a4c268a922d14a28c786b4d95272438f052890b0e6053018b212a0c91ad2839144a252052291250698867060e3464e8985aca434e909a4428984a24348891c4d49491033099131220ad8522c88a538a724d891a31425096382,0x2850a142e80b405202901680b4052029016f4a68de3ee70a16a951a543947c50851bc38d474081e1c0e1c296870850b2025c545a3d254a71a638d9b94a8536e55a142a42857a31c981c00a1628dc8297f4797e146d3e14ebae8f803006f4142850b63d8ee3f2e142850a3530c051c54d1a54a72bda7ab212cf2e88410c660ec868ec80bbf2b602504c32180a1428dc856453b37b21d10e480e40f022c8082858a142850a32a8b43852dc2850b2026fe4051640414ec5901058af783ac1ce01f01e0450b162850a142])]),([0x2040010c3b240404012087648081030ec4208f081008421d9209],[(1,(0:Int),14,[0x5287870a10843152a54a14a94210a109570fc3956b2c2bd90e88724081c4084c00b43c5a1c285375642951a142c5a1ce8d504c82c71181713337c2f4239103882c00b142858b142142172c5141480a4051428573c68d7b21d10e480e40f012862c50b142142cce142842862f0e14a42a099058e23069a4a142941314385a1d53410d00628288060e9d4244880e1038b0d243084c153048c113064a22248882c183060814a842250312a8e4895070a1c44538109d22428909080c881148f56139e4279c184640c843809222712052494c49064786c8dc92a2456e09d12c2684944902504ae78a122408890389852215088f0388510621346898d0930845893d82,0x0]),(2,(-2:Int),30,[0x70028d68d70a8218607143c50b142853550516533908082e4081c41b3a0810203905601d380142142858a6820ad2ddeb5f172a07902080e2c00a14ff1b162c5a7e284c70b47a2180a2ba899e90383002850a6b858b162c529c295e342d0e1520b0c460afa1c2d0e16af48306b94e8260340312124c8109820390a8204121e287120e1831118183850e343932e48309061e2d01859496544051cc874a10a46029d6860e180c752080674e122e4438c0c3029c28243891e726111e1211086240852481440d381091111308032244491112850938904473a18e45244c4a1d182449094101911242381b41ca072c1cc0739502891c1c60712303fbb01d00e400e012,0x22858a35a0a3668ac8ac56c413a040f203905603d0188073e050e142858b14e6434e98f34e85a1c2d2e178f483071a0a2823bd20710207032842850a0fa0ad795f373342d0e168f085a1c2a099058e231c3bf69e84722070029ba868535cef5e75a012008])]),([0x1],[(0,(0:Int),6,[0x8429421084210a50850850a527105484217b01d00e400e00f0021421084210843162e50b83a508535dea0180872850872e5cb43d0e17070a1a048850223c44c2028848100c90221085020c08242240488114044810c041a22364848a11448911204451114242890914803208a110626348684d05b125248c971362704c851a2789061342504c09122a34848ad2582])]),([0x1],[(0,(0:Int),2,[0x2850a142850a14285e1e87a1c2850b43c5e1f87e1c34908c24308940c28294044810a041912622441881189a634a680dc13025049090582])]),([0x1],[(0,(6:Int),2,[0x8421084210852e0f172a58a10d0e9707cb943490923048a112830a10182260914304860c51112214418e0d41a2b426c09412424048050782])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r6_ok : checkRowFull 7 [7,15,23,39,71] [31,63,127,95,47,111,79,55,119,87,103] [8,8,8,8,8,8,8] 2 33 [(0,1),(1,2),(3,4),(4,5),(5,6)] (forbUpTo 19) (RowSpec.neg235 56 (-2:Int) (-18:Int) 0) [([0x32328810471329008470b2908046a320810469321008468b21080466318810465319008464b1908045a2a08104592a1008458aa1080456298810455299008454a9908044e21881044d21900844ca1908047810823283f41081b283ec10821b03dc10821a83e32b01083a2ab09003a1ab1080393328108392b28900391b2908038b2a010838aaa0900389aa1080387298108386a98900385a99080384a],[(2,(56:Int),2,[0x8421084284210a14285220422042204220422042204220422042204220422042204220422042204220422042204220422042204220422042204220422042204220422042204220422042204d010ee9c8e3b0e3a8d9a8e9a4e5a4f198cb70cb64b964b54cad38ab34c72c11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a00afddb766bd5a7467cd97263c587062082])]),([0x1a31754120292c54ea60425254a5d4c840a470d3a181094a23b08104613b1008460bb10804523a88104513a9008450ba908044a3a08104493a1008448ba1080446398810445399008444b9908044c3a190804283a3108042439b10804183a2908041439a90804303b290804032b8108382ab8900381ab90803826],[(0,(0:Int),40,[0x14a5119a384a252c24ac18ac162516190e7bc290bfd93c82d70924a703152045708c4970495251f4d73262925a131c133d87eb8e54f30f1698be4c094035da35e5c055fb3369c780eb7005562c38313164c5845582c4c2c382c340df67ebc2a1c2613230a4e02f95264d19062948b8ca8670d068a858f54fa67d95ce2d4aea979a33062704c68952499ca66717a94c9c2c1c3d4bec5e4ceb4714c28bf58fac5183bd930cc5609518e10c86a41da8fe51b2cbdc548a32492c88ce01bce4c468b061b04c68233270c21ad746111fb32498aa146190dc0587054689bdafcc5d72610762975c350a3288cd0c950b150c5842dcc5f4afa5bdd188c948c960d1489782,0x73f00253c917920f24580282e9e8f6be870bc3858b57e80ac0457f4e34294fc7d0fc3e808ad3e372c0096f18be313c61f8c2f183e303c6360050b1787e7c6c50b2020a16405c3d8c82952a352e5738d571a8e34dc6938d171a0e34d8183e0e1687a1e80593a0f0f202e1e405a02929064041740517405a52b0159682e9682e8e86851bd506e34c414df921480a6d548d82dd6a49c57e8c705e06748730000822e45984f00008226430721439061c960f8bbd1560e810e810e810e810e810e810e810e810e810e810e810e810e810e810e810e810e81001d061c947518a4a6407c58aa15261523151c151a151909fa3fd1fac5341e81ab80e264a263222a93825,0x90152e168fa1c2d2f602e1e97909550bc385d0150e162f0f958eb05d603ac160058bc3cde82d0e17405ffcd0a1687a3cadda1e41563ad016828ae86868d1a166e84b8790170e142d82ac0560a0a16870b602e1c28590160ec7384e701ce0b00ffe7e495a121a3643520a0a16424162d80a444346850b43c80ac256028b2020a146d0e1640543850b43e5738b57168e2cdc5938b17160e2cd81c3850ab8a0a16c14374156026dc2d80aa790505e7c2d2e142d808285b090db015808a70ba021a16970a17970b5668d1a1687b0105a3d2b1d887b107622c0d0168082c80a285dd118edfe8882d2f202e1ee85d0568282dd9056848a72a0490550f602aa14a85b01,0x10590170fa02cd91d021d021d1a6808c9712f0a146b6f97e80b870ba021a162f0a160050120b43d0282f0e164041e1c2f5e1c901128db0560e942142d0e16c05c385c1e28563aa17540ea85812020b16878a146f474087409a020a17870a5b9d37e2c80ac0476cf2b67c848ef4e5740414e950b202d01050a53850b17077b876f0ece1d7c3ab874f0e8e1cfc39b872f0e4e1c7c38b870f0edc03c514fa120b56870a3429db1550fa120ba0a8a378790d52f20a6be8f1b60ab011de1ce851b6020a7428d0b43d82828d2a142d0f83b9c9a79347265e4c9c9879307266c0d01580a40417871b105a1c285d01680a4242ca90d582b404146959ba12d0115e5c2c5,0x72e80a2850ba020ba02d])]),([0xc10082a343a3a4402068d0e8e8900812343a3a1402028d0e8e8300802343a3a03020ac90e8e806081b243a3a014204c90e8e804880b243a3a011200c90e8ea040431a43a3981010a690e8e2840411a43a38910102690e8e2240401a43a3a41010c870e8e504042a1c3a3880c104870e8e202840a1c3a38809100870e8e8080843b2a206010110ec86814040443aa1a0614187621029048710208828720108c4830ec2405214261cc840a4304c398901480c39080451218752102914230e82405224461d0840a4910c3a89014860a8730212924450ea04252890a1d8084a450943a0109485a],[(0,(-2:Int),285,[0x149838d4249884100c4a608444a01898a8426890c8b034a1ce4f70142828040521381114227b82314068a0c93111a05931493ac0b28452528284302d21e10fac6d430906c9c607da088b089288888c0a49188c1a2a16860e070c01930912491198192a18461822992c098c14231c0611148a8a0b4c08c41607121881e9484898c0a1ec8464c34381a2610482a48682e6c88c924a180184c4109489a22a309838082a080f681c511060a2451031106410300c5210482c4c3224325016080c62104310300a600a164868c22068202a202c20c0348c204a201d8058c840c0592130a0988cc14160a8e01a42522983006180d141521981416180e149c2530031e02,0x21aa181c28c50c8b28493261036aa1290d40a1315141c0c1c05184501990f8e2b00ec667b19613161b0480e98888c620b2a092a05868b4a007cc262425842382130280a480a280c281c4c22601246303858521c683258184450601c585060d541a142322322226283428382832345221b814a5249830d430d811f3c0196018507131d0e4614018a8c144292d4139409390fca2121c1205e680c28ca30540d0c188c190c2649307aa0e188a118a0161c1603058b1504dca5e663d2c09242a24130d092238340d033b82609fd70d0cdba1b21d0c2c8c1e091c0b3218217b09212110e8492121c0297ab7012509806b68a82231309428cc3049034b8aa117dc128a,0x9984916091509144904861c09940a88c514129b06980c9446188617071425189402bdd0c868c4d0e4a0c4e148346430344c28e058304c172a7c68fb27d59e8de53ca60192419a018c42990314830e018b029139983449ac23028181918546807f548d24b52130301822f34a212159b0512560b0c8c39ed08c98429052121092551354121c12149223120e15241c24907d92c88a24444c6424c22454246824c4245048a8246024c04c8c48c448a42cc8308ca0e1888aa086c0c058e150c828302c32141fccc8c683015d697b93163ea8065106452854e60aa280e21282e0922300c06348a2e28211621342903109410922430140b252c140d24062443241a3209,0x64d45eb275a4a00b88656c1634140553459070a928a150a8c0b1464980d0e1902e9e06464582b88f962b434620cfa3e98c5895eb2f4e7a4fd93cd1c49e23718668e1ec6f5c72ab553aac0c4a0c2a20642049204c20101a4620432051382520101c2620380a6cb86bb666b84c384c72609a21186c9c485068984c7c540a443c49384144540c493a4a126c324c4814f68952ea92209189521093c9b284e09eb0c89522910a9a87168714050845120e9148988192068c81908d12a30681949210861085909305448602905812a49724930c1c030a5112921207148c833194a4b928c32061ed2904168602a49226126701615e4d1611733250b04944494131411960,0x505fd8fae8344b342b34524443461914341431146a0c541447e6d092c06304b284b2132212a2642212318892c46048504830c15305039032d4e24c232982cc2346430c228091883118b25a3098b2c233113398b310b2234220d28a324a320b80572a520279e92043c91e64a4251c0c09386131491c093161152434ca317bc07146419640a949222921618888a0890591908948898148708894888888a5195088a8894d8980889089445960a950c08c495149a4c928c04c49a2c148490c4894a948e140f140e0b09064904858a91864a928919091a09090b05860c060a86053598789430523029cd21815185418615070c864c427d456a37531ef05032505834,0x28a032c14ba00d202a202631102510119020233090200e22902c052835281b1c062a312d310b0a2e3106063a052cd524c52b3205685284e84a84684283e83a836832806802b4061610289a34101b183a18080629182d161e1e1a1e2a1d189b149b1e1602e82a82682281e81a81681280e80abf10162920464848304d30649a48747c9a708848724d704687656345c3a683a66345e088c30c431442373054170e904c908f1356928f0d069a46130e98061a1e184e10519a0e120592529b4c924d1b0c1109090e090a048480fda0845c6092ec94e425aeb32493229326a30281212a6599289301c3304986188f5c3ea3f4a530c91305070514a18a050e4505051e,0xa0020226c1c2952e54a73a4bb7284e9293e92a591e874a945846ba25d6533c5c51793ab6b5fbd46b1cc139807302c000081f31bef70cde199c32f86570c9e191c31f86370c5e189c30f86170c1e19b81952c54b972a5cb972858a14b172e50b17280060f1b2c80a287284003046d972a508285ca94a0a151d41cb2b8348224af80020b1903741b0c6302f2135098e15a48ca3638a628c19926c312c13a18c8b6388e0a010a790014063c18918a604a7e4a714004c1031e01e42c11a08c83638860881001107dda0222043a04b0150e44087408001820e0ab525ad1d0213022d0be813e813984148a9387b7fed9089d2c445c59c3942252e5c484c09e02b0958,0x20fb800204cc00002de33c2a5491864980010377650a5ca2a539905000812b6d17114a8384376a5f176f50b1d40ba807502c0c1c2862e009285ca000846e0a5c95e1ea0a973002c9caa340248d050a16992ab2ad4852c8e972928a2a3292cb4aab24b90b1bd397cbf6fdd7ab97e8dba156b9ca279447285e509ca079407286c00800211d928004091b2a4ed4a5597ac4e34976bd46970e952a4bfa0550e54144942c515553ca8aa59f2c2a89a47429bcdca35ce295c5238a37144e285c5038a3600000093830433a0b15693a92abe8c134156a4ad41622754be35ee15bc2b3855f0aae153c2a3853f0a6e14bc293851f0a2e143c2b7022a5cb9400108ccb6285,0x50a50a00404eeaa00083cef66c22bdea305537f8f858de269aebd10408aa1ec056d9a75ae08ee46c5ea9230c9319528004137b2e5000813327e000026e53e234165951144da7a2f2259652a147123a9394bf3ab5ce315c6238c37184e305c6038c36004200004de086870a14000074cd52a7295a8b492c5e545f431a7a2a229da8409ee51450a69dc34951a53ab4acf288e50a0a0794072828ed7488e905d203a44e000020f38a8432a0990b28a742b239124e351e62f70ace157c2ab854f0a8e14dc29405270a3e145c287855e0060041b0104297284004093d16285765780020d192a54e4aa5471053bc56540a2bc28baba95265332b2da4fdff410a05c000,0x52bd69408aa4e9468ae92eb39c1451785092692a3aa2b6ebca0827b6123ff1859872a5ab155048180001052e66914117a9acb285162b284974949548ca8dc20a20f57dc5d7fa65fe5a753c407888869109220a260450a1ca142152800213ba2e50854b755f000810b3b8a12a000013304e775c314b5539456de6132e6cf290a91301085000015f00002278134aeaa28c650010293000209f9286a800208ec2b2ca57fd57c66583eb8e069b7738a47144e28485038a0a573924f248e48bc913920f240e49980940010a3c5380020978bf19504c8af6a52a33c205cca76a9792c8af1a14dd134e9231d1ad96963942c280e5051dae911d20ba4074848311801528,0xa9bcda6bfa000010b245a52b84aa50ad4a49251ca74a73f39016089a9516d608ab7cb972e531dac4bf93f00580269fdf7a5feb29c6850a142f5738947124e24444838909573914f228e44bc893910f220e4598094286280021478004053c8d22790cab0789c9d5ed3f0a6bac5d1141e6f62e533f199e931f676716677637374e854c0906005000028b058a000028e4a972857a69217904c934e27528aea2f3ed34935c95249249e45f82491a527a7e742ad4a50c63280041479280040a9b2e54a12b575664fa48a496f59e04513c68f641600be9c2b0048e2cbf65b8d8714329debb8dc2f5738957128e24dc4938917120e24d80572a50a4aa0f145496f10810,0x71fc7f3e5c08c8146e289c50b8a07144c0b9d00160a5bdf7d573fc7dc09af26a4f01131e58e9f015dc2b405670ab0155c2a405470a7014dc29405270a30145c287857602f0bafb691c0b9fb1158e9f019dc33406670cb0195c32406470c7018dc31406270c30185c3078676070e1687b01000615ba87a1f40543d808f810003054d602e1e405a925915809b7b5f404a9a37ec6522239eca48409652b0113be2b0248cb8fb1d72fefd8fc39a289a10af26ac262cf19484903627246e27c539e817d06120c1418073030ec8502ea01d4144a92328d8a4ef0ac00260f7911686322d894cb09c29a7902f201e40b032a50e5ca14a142852e50a1085000028f042a54,0x9cff0ed3970e45b21130272e9c484c084c284c48dff5e4c196922604262c260c8a4c49359024dc4938917120e249800038596f0100060b58b81387b055a0ae35162cdb015c8ac048c09622b117c2ad144d48e393625908d544c09cbd8089832c644c884c084c284c5916cb44d49e022614aa4c0916c044c395528db2140e28295d449209239222241e481c9093b5d1242247443e885d107a2074401a070e5c084c080038586e1eef8089cd1ed5602f0170e4c09c3b9f6a226a4b01580ac15602b1d5b8ac1577a736958cac85e3ab01130e1f3e580ba7e7dd146c09d7c5b05590bc046ca8dbf86ac05642260cb015808b890981099919852c544d49c393161302,0xf8357069e0d1c19f8337065e0c9c18f8317061e0db80142e50a00305bed1d9d112a516c256fa4eacb095848d81387b0903eac0583d80ac4553f9fc22221cb19788ac15402242cca4ca84d1960ab017009301188b02bef43930a1112580ac8560ab0157f56c24af97e1c6d82824c384c084c784c084c18bc09002261c91d45e4c19432c1cd7e1c9853414cc084c196022424d014009ce5120a23942f284e503ca039436058095810b8122d80a2d80800b0b0d6022604f0d72f75cf002c11b72f602260cf017809c7f9d580ac35c7f3f612e1edc560ab49780b8fb057ae5c29602b21230e271e58089812d1516c14bc08cc285c5935df26446dd9872c148c584c1,0x85090a071414ae22484488890792072424ec2443e885d107a20744452a18c8b625307a138280429e4004416719e19bc22f844f087e10bc20f840f08d8143910278082c590119021302000617d88893d5573216d1132110a5828e850d811d656b22e9c14d50e5419632b1f4652a22254f29712b4153409354877d58b34b8e43968ab39390213064868997297e1ec0454394ba4e54385c188c096fc04a40489060c0220422044a00405de2294e09452aad0f4b8dca01503282579aaca5d9280152f53d86a564abd88a134442960a6a44192926a6d222142eb4b091416706a20538d44408b4d896c24b409a02221422142e04220c50c645b1299613f706de0d9c1a,0x8e9b599d576ad7ef52597544d60f95de06b2e5eb8385fab7aa0319388595f45c4bf84c91e76932a372bd576b92a0ca574be34a96c7c0925ee0e74af7d06720cd4198832d06520c9418e8319062a0c3419580982199053f46d02e82350f9e10b084ebaa1330dc2186830315945108a1214141428eda48a4912922124243448489050028000005a607504c81948fa00001176aefa06e40da81b1035a06a40d2819d033206540c681ab022840020c4c94293a96f2c54ee4822612ce762830b2e593dbf1710e68144a782ca215a92ca470711af94078001016f29f8c53497a41e4579208b34bb95e762f5246192606c0d690c6000108ad2de429885290a421464288,0xcd511648b1c4b0fa2e5cd1536ed57415869afb2d77fc3b3e9d121850c196581e3df5dbd88b8f6ddc7f1d116387b19584bdfb0170f34cfa2d244c5a0ac2569a90d1a28f010c0882384e00031f8c002848e4838006418b56f47ca095548410430cc29f600520c7876710ae211c41b8827102e201c41b002d0e152a50a9421528000193928429509248001048d8029bd2a6d8b692f50a9bc7e4aa4b172e531c545b52749d5f71d5d0a99956b80a4bcd77acfef4f8324af69f5a19dcaf51e874c72a7e77a9f812a1e2c588d2a162958ac2126e249c48b8907124c04a142d0e1000c317250c80800405ec93a1410597cd704965cbf4964ab852b34a75992e9aa5ca4f,0x36c35632c9c98323f2614a0d70fcfc0ca3f3c048ad79738042614380ce5e014a28c8b6388e228400709bc8d2ffc003069dff979e36e6a24aefe1e8c0961ac5eed0eb85414dd2bdc1b38357068e0cdc193831706100cf8000583d6b013b68dcf2c05e52e5f87f01580a6930673ecc584c29602aa4c996022634261ce1f8fb094de1fc15602e1d9893a726044d11111739247244e481c909083605b2ac244da9c3f1e4c19e2a7be6cdf1d76fe02f0970eeff82aca5c3f80b87e5e6f2f60275e2b9c8a39127220e4478000f89be009c1075e8a2b3520006095a6fbe4c09632f89454614b613acbc45cff3f35821916c711c3d28007073cf9ab4535fe3fbef3f3edf,0xa8e145c2840536070fe028bc3800e1a9800b08bc4f08eeae3dd557828a6c19e3fcfe02f1eabfe4c2957d644c19cffbf75d04d7d849a72e04e1ec35c7b4f602b0d70e890c286382e000b0d3d1400b122c6f2effa72674664cb2d172a784b87460c260cb0158089871fff0d331255b1170f36c05002b0d4de7ec04d7448e885d103a222104c0000c35370f17879b402000c1375a4afa49fbc08007056deffdfc3d84898f09a738f2604e1dd65d3d8a9981198909810d8324fb096008b852c1560247c3f0e5009c3d88a2c04a02583c08ac15002488b1110220c58183f0fc3f8080060d3c003831e56d79febf7fd3b5f4fa00341172c89b771fe7206c4bcb85bfba,0x12586898319849109139207243c0b0170f140050dbc001823637d05e1d7a4eb8a2a4a5ffa9310e08bf39e5544c29c3f8cbc05632b0178882d8a9bf8b76c45e3f3f60a8b34a8322d8489811d85190a26142c280e5051d98911120ba407484820925451926f712c000e1518565f780060c5befabda7363cf7dd9568ae5f445e393065569cd1536add48b6188e000306fc5458f0a74d7ef602b0d36fcfd868b832c05c3d2edbc84befbab7884f105e203c444104c0e1e280161b59bf004c17b39ef8a8bdfba48997387003c12b139a586b87261caa692e9f8f34179f378f73f87e5f8f2604e1e6f0f551852c05602b114df0170fd7c5ebec0563255030806066d70,0x26b429daf9a0c2a5e4346badab7978a444893c96a973556ce98b55491a28c93658960002049c6ca7bc7d45f9a08d71b5b85afe2ade5eed5e1c2c54318470001822e1713de29244385494d4498000c3730209f7bbc5248170162a001c19377ef8a8b60a769596b977c15acbdfb6117024a48f9b38f260c2634efea930671e4c59e02f0d70ecc08cc084c4960a8b6022614e3e69302580b97460ce5e87b0d580ac252029013302784a2f0f1498109872c45cbb308a21127220e4444413000030ded75f7001c243582ac3455d35652b1176e732b657bf15d85a022bfcb4ebaabd7fcfd3f8f4bd829a7b015809bfa3cf813c05602b055808b8102856604f15130633,0xca37174eecaafcd45fb8d54d55e56c345640455ee199c32b86470c6e189c30c06170c7c00a840943850b140050ded602aa14a9c48003047dc7cd2ba4ba1131a5de2fa75d0578d132678cacf9093b48ed1e56404342bceebbdf53aa49036387001437b05a1e2d808003069c56aaa88009048c68aa7de04ab2f7daf3d51a4aacd9ad7e7e446923a8b764a5212e1e2d5919682a4352224c090601d880030a0d8bd3e36a55150e77d5a5cdf54b9b0aec80a8790149ca43503a90553ed3c84a879a36ad0fe32a1e4053640534983242518a54295bd0ee7248e489c9039212124c02a04a1e285a1d280081bb8005068d222049484a434ae24991a2abf5711aca415202,0xf20290150f166f0fa02901058b2020a54093787bb162cde1dae911d20ba407484824904170287a1c0010e9c4408001835ea1cda5479cea87afcd8473bc48e64d7b4f55f7a5e415212a1c6ca4a6990a0df9e97220caad3c0aac25202e1e405362dd90151e54ac82b87220ca9e8790150f47c5ab20aab21a0b47c58b1640543f0ec72252441c888bb5d0a3a117420e84844230287b010dbb7f8baa875595bf569769cd1563d1f2929011ae5fd5a3c6c80a2c86a02554c810c810883287909480aef0f20a0b43c5a5e41417c1553d0f20aa1e404142c50b22290d70f36405162f1f202739147224e441c8888826048080070ebc3d25b91fa953468a6bccf6fcf24a,0xea410f1e09a5c10cebff470020b50647497767c02a43464886079202c1e6a5a3c2bd55922a24242449d442488417002c80a2c8080070eac00283760794e8a7c5cfd1eb42222c36136f57c8e8b767764e4aa229d5a5ead0a8f979b5642520275eaa8a30c8b015773bd1d88007044c7b9e69b72a956f371fa1eae5316004542c5b1da722142fd22d862383c1000611b9ef36937eebdfedfd0efb859b4bc5fa328b47d0f60277e87bad3bdc2b385570a8e14dc29385170a1014f8000187d6001c2772ca8d94ae23895da3da7aad395164dd010529caf90555f4795f4fb5ed3d0f17d78b47cda5e34f970605a5cc81287bb202a3e87a1da7901458b1697320490150,0x5080d6bac6a6c400183b67fdacd75c214b7225c54554f4bc96a41514ff1bdb95e80f0678874a000c15336e64d85b8c88d252421b76c35cfb4f53b4ece87b1dc7ca53d0ee922c245248a091292242441c8888811764a141422e841d090882195bc127822f041e0a08801d027e46a216d00020ab8db521abbec732ccebe48547d0e6408566d0e67d80a8fbbea8535e424a13a426484a9091211a4c0003c3af4590150e001837696d1c2a6e5ef8b8a8f16514ee7dd55114e14f7e1cabc29bf3adb9bf43b9f4791020dabcb956deee80aa744381c11e4866474a95d482b734d7d6e579902190e55f5d9c92aaf82a9775e2d5488d111022145801400306ecff95aa,0x1d83118111851d8b1d810e8911890e81118b0b810b892c054f910e5e431916c711c00000e5a2800a12b8aa454da4aa22feec82a444dbf59ad39be6408642943d5f146cda1e00543d0f20a4ada1e87a1f34785e1e87a3cafc9dafc3d24614e90cc715845cd8702402d6962554d8473a90d1bc8c8324346da2a579f22948d5f47b5e578da1e2f8af906e20da41b0835906a20d2419c833106520c641ab032c50a0008bc6000c16b000a085ace5d4d34a3d1f9ff5e678d8a962f4dde7a3da780173f62af1e3cbb6f6394f87d5e152b80403000050eac96ce42d239c00307dd6b8b8bdf38d0b28664766dff2f85a5c21543ea6a8f9094af16ac58b36295e9ba60c04,0xa04220c3a04a3cb811d811ee159c2ab85470a6e149c28b85080a7c05e1175235525968b870ba711891191118523950b870b812c348c1961a3a0c5e0ca5dd811d85190a26142c280e5051d98911120ba4074848209256f109e20bc4078888200140460400443db5fc629da1d0211324d7a174a176e23fa230e2326582a6cd38a90b810e811a9508812c34ec28056801676b42e142e04462c468c4604b29291e5829a8129f2e1c521cb21cb0d170a582922608810017067c5d085ce8741907254d596902e0017071c5c685c78edf88c18aaa514649b1c4b16aa55d58291a91183101e00fb000c07d80162f8cca3c03ec003172a1726173e231e231a010c0018b81,0x285008957812015439d022302012400591870e810b812004d408ec085c485c0804a800e80117063b02170250e7428f706ce0d5c1a38337064e0c5c184033e0170e7f897a475e9612461ca7cbb50b8708811193359d0b8b17870e8133811d911a912ef2e04760ca1cb891a8711850083000c8ca9cf97061b0a1d0214022312230e23027809d812c1444088c09602ce1446042e0c8e14d053b123b0217020136003ac047409c3970258094851d811ce491c9139207242430980a40800b8b1e2e94002c1a3176a172a2c488c52873a546accabda831d810b8111810b8f2f73a0c4614b0117022302230a5829d811d8528746142e0446045e0c520c2e14462476243,0x1c49479190dabeb769daf8aa9a40785510a8920e0f04ffb2060300184f3800a093b87000c10311ae155a16b5710d0a5446479dbf5adc5143488329fa5d1c0291e53254a9f0729c2f0f162d0e963a207444464888910c22105c00c00a280021f3a44400104b634d6b48974522a1d37a1e045282b6eca073efc014da1e2a22a9f90d682aaa6fc3d9f43a5f622db67940e1bf23f5c1c2d54f1f15af2fd1179c8a39127220e4444608882e0252e0400503c7002e0998bc7088311951ded2c548ec88e3874c8ec085da85c28ec28a92b3d3212410640088810a011a811d83118b17830b910883118129f2e24760ca1ca0111a11183130320248c085009c125aec088c,0x4b8da1e9feff87321ce7f8790170ee72890511ca139407282820b809420000ec655d0aa9f75d516ec826b47d4ed7f4e17695e1eeab0a0b54395f47d0f43c508da5e6e80a4659c9c387bdc2b385570a90151c29b85270a2e14f8070274d51f63cd29c2b4f36ab8e7f9ae16295e7641436a7b013af57f1ef70cce195c32406470c6e189c30b863e050f43d0e00387be00041bf05b0517f14cf1b12d295b46518d3cd0adbdde2929a7f95b5e2f9fc3b8f4b9ce2922a1473fcf75d535d7d2e342a06c1d29934f6e7169350cb29c6e543a05c75e0018386dfe876dc6e80a4147bd78a6c8690a60ea46d2aa91beefada3dbfa5e9fab546c8ea97abe8f9150d71c2a18c,0xd2f4fc8a8bf901556e28585098a1214141c28305c0d01001216b8005075c547957dc0a5f547d869afa9eec88acf349559110533dd34f70ace15602ab85480a8e14dc29385180a2e1538000087ee00041c74d2a4ca1cf6534af9fa773c8a52c5514cfa7c55574515546910a55f164055795b255feff952a247feab4f25ab9e4045f9540b89cd2cc8697edfb8fa12a7dd7b5ddfa3e9fb4d228c001e0af9df71e6ad08d241640481b000382f691d5d9095948d15939b0a8729cffb1555e3d986120c0c0c160190200021f9b4045458004834e6dcfb573abaa7456bd0e5646526a6be87d3d15a3ded8aa40547f1f63c849a722542dddfa9f07c3ea994a05bb16871b,0x49524a91575f166c80aa931e15adfcf8b20269d451926c712c70e002872e9c95cab879a36a7711c6a57575c791d245b0c47114009076c00084fe3951b28614e820ad3bdf47b4f57d5f35a7ab4bd3f5fc8e9c79013dc1b3835706900d1c19b8327062e0c201a3022950200061fd8d8128fd09132200161c18b890db52129394a4bb735d52e2aa3de2c5d2553f43d0edfc5222c8aebd3f3640534ac8aa87a3e41543d4e4c192329014da7e434f70cce196032b86480c8e18dc31386180c2e1938143c500143f7000e0e5a41454485578543cf69cf2e8cf0973f14b7a5f872adbe9c8da44489164244c0960a3ba4aabfb78b47c96bb72a14260c7fe6c5ab3645557,0x7cc9d29755950f5bd809a791135f53d0fe3959050d8a64086409e0aa1e44434af9b202bba02a1f8fa7e8fa9e8790537f4b8d221476916922c245308a4112d2252441c8888c111022ecc4290850508ba10742423084410cade093c117820f0504601e80004881e221c955000a1abb624ad23511a49afa1e50526a2604915459111ee5644464086408549853c50b43c80a6d82b4654bd3e6409a426df9766114b229044446088b11105c00a0018896d0559f61a3851b2a4f476ef2a04921453a63d0f4ff1ef79af53d2f212a5e69922190a37ecc249649209090c12164c0a1c0070fdd638d48009045dcfafa8005042deb23512ae9d64f3cd71e44553c809cf7be,0xa95285ca942a5d0145ca142a50850a164054384216c05802c01600b005802c01600b0058022804005044b046850a12795368aa70be8000121b6a32a76239ecf000415322ea67db1bed7ad8400e808254f001e0201840206c00b94294285c1f2d008210a1087005802c01600b005802c01600b00580200443db06253c54aef93ca19575c2c6e19284929eafcef2cc718505592aa674c914e979a08d551bab4514de93cdf3ba6f13fdaa94818ca00107a60b152a54a943142842800022582a4500853c85038003821627106ce211c4138810100e20215ce413c823902f204e403c8039066000121118ce30009058d4b8caaadde])]),([0x40330e24052040661c840a45],[(1,(0:Int),60,[0x33251c2918461c04990491f9d024303883ea624233235106202180a211450061402080a700c080620342016202c46202c2050665222302849444610425206f5823110c13e294602b9e190c160c150c118c11449cd09418f46e392a02f949ae2b02238486862122c4c12166112600c41641414700a423026201014213842504218243429242118111668a4501c509214d41db86c09fd4a4429ec86448864870182a50f61b0180312192109213422282412241120a8090c3011088c300924313464141610ea44688889118088c11089104888a1046084a105518b0890484848a090a0894848445084c05396230a23007ca1344424501203d60b03012121801aa02,0x8a2c5431461c2a07868ca26461495248c150c21eb2a49a2a13248e16147991cb2e4e6a4f52c8b12629f55731b535ab2c51e25714d28d961c21d54c299f5a7a3bd8bca294706a0e428204844c260a0149844a824c20c3018d004928ca884c24ce214980494049004b00c6804700482a44038403480984828700c1018c8449058202cc24070149054c4408a40a0e072504440a828201888602034944046405450a8204c202c20a2204848846446680e2c470242c4168486046604a604560300a3054301c49603058304c302a3026301a22c510bc34182601c1c124424c2d887c684c28c828461a32247a1d970d051ec3c68cc24460e1a0c72c4a83291928c763e,0xc909868209484901892946020d018e0046404a018d00c900ca89890948aa0808c92808a808058401882884070544080c8c04ca030c0f0aac0c054c420f184e370e164b550c0b0a4a0d088b0889084e4204464c014504ca8c0a0c0500cb0c0a0b0a2a0a460705440545240d040b014a09092405014904cc1ecc204320252041582510481c7010451023101510611460144c1464104310131044f43d21698f0cd304c3058162c1429145210321042f612c212611132138213204e2145e150487088c84a700a086b726222191215148c182910f2c0585f124cc17006c45521590a6e460626052604c602a52304a303830344370609460a2386441d546a2b5132d,0xbf55154f47dff43a554d16ef58ea05d403a8160254a9687a1ca8122a50b43a5a1e87a1d285a1d285a1e87e1c000060c94a8112d0fc3f0f4385a92d1e0ba4856254e0748a3143d0f43800a0c5b40437a3651d277c7a9430b722204165059552ce6bddba390c684322d910c4a62435c27000403260a54b8021a34a0a952854a2aa4b43a50a9450415dfca152352b72a7e8530612e5080040919504fbbdfb1ba850c305c2cf1438e2a30c8990b04682320d8e2180c08b0218e0389604012c2d33a2befb0d4580934fc39e8094804c8054b08080d0201480cc80a880a4a2e092c484c08484c26484447018c80420384458524c544484c49254c44c964452145804c,0xa152852842100001a325ca14a942854a952a50854b0324dd6d1a89b5156c53a946d02a05429a2b00a4b80a0ad42d009373a97284125d42a4f43e54b1d807b007602c01a56532d2bba50a15ab5ca50a133c2954a142d51e5cb952856a42856dce85ee15bc2b3855f0aae153c2a3853f0a6e14bc293851f0a2e143c2b7002952842854a001837ea01052e0e952a53a1681492a356ebe0c20a97870a952a54b87d52591db1e570a139c2853b96dd3b52f803f003e016338957128e24dc4938917120e24d814385a1c005072d16878b438522040b1787a7ca833c8572aa3e8f55d50f43d2e2aa05151e17474a7a01f401e80b0340514285a1e280020eb829e68a81,0xc833002a50a54a952a58a14a952e0e970720040854a10a152800610392a54a93a35adf942928a892a50d02b9b54aaba5ccb2a36824946854a1468529eec52ad6a10e58d0eb72a54e50e5cae710ae211c41b8827102e201c41b012a54a952e5a010400107cc14a1a3d3746d5aad46956f37d2d2a180105aad6a5fa9f9729d4a942856a55370a9428d8b96b43958b942c42a5e172e2fb46a5ca10ab7845f089e10fc217841f081e11b012a5a015008295280040efac0494cf0a4ae5494e6798e2f21ab6414b42142b425b9ee1528429fa8f946bd0ad62950e5ca5528dc872c0282e1f942c5ca962ade217c427883f105e207c407886c00b4024b20290125ca9707,0x7021e05b8014a942858a94214b14210a54a16404152842942800c13392849145b800408192e2e356b40a2854bf69a0b0749edad9a08aa3f2c0290f0101c203040408040980972a54a962a50a5080001239285ea95aa55a1a5cff0a93f0e59a0a52342d78aca2c0682126134eb4ee3ca8d1e56bd2060280041258002058d1428c5f4d41947b82aaa842c7400e8080c10101e0254a14b1528000119a874a14214a942858a96872a1000012b254a951a32b170a5ae57aab950a97ea5af49f6c50a12be2842c52e54a562a08c320c254a00104b64a9428002099821079052842a2caabee939c6a4e90a10ae7108e209c40808071010ae7209e411c8179027201e401,0x1d79f62271fc1496e90167808b8b1e930a13025809411864188b94a0115dacbda577af0134e9795596a474dbc571c98f387c057849778ad7a444042a4008b02872604901580a2d0e5c09602b01000214fbc056028a6ff5fe9ae3e72520aedcb891e7b59586bd73414de1c98322c8ab4454b930651f43c84829dabc2e80ac4488020c0f0145e1e2801e14db87e1e2f0fc3c5b01580a415478ec8e056020b16c2564ab051aea2cde1cb7f7158eb87265479e2d80a4048230005856e90158082d80a9f001c153680b87e1fdff6d71f22a26043515574172f602b05588ac25c3bde3f87e1c2a82320d8e21f702de059c0af8157029e051c09f8137025e049c08f811,0x1c3c8082d80b07a1cc812c0583a5a0113020432020800e16f8f8b200583f0282942a40258cac0580277fb7b0d72efc2a011b0275f60290113021302580ac056ca20240f8a9583397445704b6f0e4c1997872434a0905ea982983c8caa9f0e1c0a280c9011202040047804c09c3c5b0170f6028b1787002c2bb160225a0145b25582ac85c3d808d852c656024654b015d7d5452604f0178095fb75580a2d82898339f9]),(2,(-18:Int),23,[0x23201c2803201e201b2026201d201a200d200b2a21101120342c2128052c052521212918031c063006212820b22413110c340322212121111810132432380808032434101622382a082c06280d130824051415180d09082101080d24160a8828090909300c111120aa20b428a411192190100b10152610231022903210249022093009212c251114031114300a2406111c2212149410922a09310822301514188c04062908218810941212240328062231220a140514121098080e300530882414288c0988121a221120b00a09280a141104051219108c12982130088a090c119812182d2ee01bc033805f00ae013c023803f006e00bc013801f002e003c03a,0x108810e8108810881088108810e812c0560222043e04b0160f6023a042204b01455604b011102580888108173872204b01110250e44087408481874087408740854084009a0a4b20a8b439002208b0218e038b1545d01700ac25602b012e406882a0b00c400ce404d0444038d244622c822458444c406c20b404426814049288c034d014c8047004440498049898949898948a84642cc8246624d404c004680438041d88081a016200e2431202c2029101921382920101c202a20b820322025282a36502228300e21241a0a1108292121342826311438061c031209208a3410100d140614143406190c2108208819880805211015013803300320ac38052e012,0x675888605a02d015868a913e72f41a40058b43a54a9680494216870a9422f24a142d80b00497004962a54a942f3da9c1d324a90104236ead5a152a54a9569d76f682496295885911484b2e0e36845c3e1f14370106020215c040808083b010104af8202018017070a539d052843152f5af53f6b162952fddbd6851a17a95ec54a966855b14ec54b952a58b542e50852ad0b952e50c41b0c4300142952a54a3320a14a1ca10a67b58fc2a54a9428426ba50a34ebd0a1c850e50a152858a35270a172858a752c50a152850c41b1098e119031602b0106c041a1ec05a02b0137021e025c48e81148128722046a04220422042204a1c8810f81088128724040b8c88,0x2043a043e040b602220422042604005410b45265ca3faf221c22146fc8870a993c1561a6bce810e81138d088128722040a44196028a4c49a02f0152e1697320422043e04220c220cd0525021d124848f81088112063405ad222acd011d1e51e7c08740960222042204220422042224223cb15292651e74b8841943a52204201c4888101010042152004981439d02110258088812c044409602e1f07a012522042204a1c981080130722045b1580888108810c850e972404440983910217065808b852cb4444942aa7cb8108833c94545858086c18e3c5f055828c813c04146c4c01128102f82b873a04f05502b44474084409c3a82320d8e218e204220401c41,0x504bd156812872214a1ec14ec08ec08440934096023a04a1c8832d0444e92022e0422142a043a2442cc2e048b22266246a446a143e0462042a94094bb6502c205140a081250101920224004825806500c201140208025b811640464092022])]),([0x1],[(0,(0:Int),17,[0xa9208b0218e0380301a111200e101a1019241430d8315434522032282410132412080e100d080d110c200b3808320821881806040630050405080328c8201a21141111200d24301092140322222431121120a5037a43907cc8d41eb86a14648e1a0b150a090487143d85eb1f54fa9bd31e95f4a7a33d17e87f687313987ca1e4c722b913ce0d516a5b58f8b0c49624711b886c48522290b483a454a8d942c864621a905e148444ca11480b080a880a480988094808c24244058c130c128c118c11480e080d080c49090407088444040a03088282824c160a130a128484882c86028c150910c84a04054c0504250c044202cc12484c082c04460426082a07282,0x8d0862a5a1f2bdc037806700be015c0278047007e00dc0178027003e005c007806e004216285285c1c3641084210e508421084218a1cb602c1c316214394312a10e0f4385c1c2bdc0b7816702be055c0a78147027e04dc0978127023e045c087816e00629421a1c3438431a1d2d0e95e0201c4042b8080790072020ec0403e805d007a00740412b7805f009e00fc017801f001e000e801000c12b0421884210850a14210b152e1ec71020201c4042b3c823900f200e4041dae813d023a01f402e803d003a07e0042e0e160054384210850e580104218a18014008214a943972e5801400b870e580150f0020d0f202200480106286286876b160e8831ed206021,0x114210c508421a1e2854a172d0e1084343a50b4397e82108421c1c21084210852852e54b4395ed62a52])]),([0x1],[(0,(0:Int),2,[0x84218b14218a10e508707e1e0049687a01160260f9780583e0f202c1f07d01580b07cb17072004a1c2c80a0059707c0145c1c2854a192221221112112181098111410940c14121211120c12208a180a100a147a9fd41e91f417a07d01ec8e48722390dc85e42720f9c1ac7d53ea33509a81d68631f1618a7c48620b1412899604245984ac15602b10d2082])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r7_ok : checkRowFull 6 [15,23,27,39,43,51] [31,63,47,55,59] [5,5,4,4,4,4] 1 16 [(0,1),(2,3),(3,4),(4,5)] (forbUpTo 20) (RowSpec.nonneg 0 0) [([0x3821043507e862084a0fb1040c941e7],[(2,(0:Int),2,[0x1084210a1084214a143162c50d54c53295344cd14b24ac952c4cb0d2c62a94aa647189a2a68587060182])]),([0x1894a806c25258942136029644aa09b014a625484d80a4c8c8604c252c4654026129523298130949a150c4980a590aa824c052a85531260294252818b14622544c18a308ca042c5144640216289231810b14621544818a290a8240c51c084191425410831a84a43106250930a20c8612514419082462883190481e],[(0,(0:Int),16,[0xc52e040092d0f43f0092d0f43d0eb0a4a952a5a1d375ab6004968fa1deb992ac94e49b24b923c92e0254a952c4492a5a1e87a1e8751d6ed73855c29e137097847c25c0d01050a10a1ca962910225a1e874b43a54a440895554942d0f0024b43a4f43a4386b43c5b012486189c1706c14021402140214021402146e1629d95c2268896123854d12963740a806802ab4e8c4d3fbb6e7cdb37150e3470708c20d40b40940757b2a86d94d92d90c1899d191c64b161c58d0e2c38c699696e9c65365a612e169d5994d54951d50c91c997163c18ba4396ca8d29217084d34284e9e3434c8b29216495511341d9e2c2564ca90e18d9559d2a03a71b0e26227045d4882,0x200543d0e9687a1ec049687a1e87220422045bd2580153f63ad49e8fa1d6b98cac64e31b18b8c3c62e0110250e968722045a525805258012d4a952a5a1e8751e87a1e8f801398aac54e29b14b8a3])]),([0x24306144531076289a248a1828642ec113c1011491d91cc2021923b2392404124764722808048ec8ea081148dd91cc102211bb238a204123764712408046ec8e91011509d91c81821a13b2390184142764720288084ec8e908114c9d91ca1022193b2388184132764710288064ec8e90409449d91ca0812093b238c10231276470a204024ec8e90405409d91ca080a013b238c10130276470c202204ec8e88409485d91c9081210bb23a2081501764724102802ec8e28204c05d91d0880a903b2389081310764740808eca848140811d90c90322830a22a083b144c52],[(0,(0:Int),44,[0x836190c06b102a4040d286885438c4ca804684283e83a82682281e81a8b0ed11006802bf769d1a814b163766bd59330ee0502756284869e0c1831e0a314e72c4ed421c08522182a693184a60b1c2422401b41941741540b40940740559587008254f9b2e3d4a86891528614b0b123858c8a3b8987128332d186551c545928e3238b18d35d22ca93a6abc1c652123406b121a10c841428c06381460e3014a25c6c2196894519c8c06868640e91612954a9ae119de3233874b0169e092438d2a3428d0e3110644285499825606063024c0c22500e5e220a76464d292818858217046991112308692a98a59121814b11142445d265c0d284889c285888c21308e82,0x2841b410a8eac2b42c34a528573115889c436217107885c00842850a941d4152e4114146108525384212a97a4a852850842bd82dc1660af055829c13e09b04b823c14e00428428420c20b309a68214c51a50852f0b15a556b3983cc18acea1750a1b5b06d81ec230059414285285a74b3787cbcd2a5ef4a42842142846b9e06f02f80b0c37a183cc18ac8a17507a851d9e42f20f91580142c5169450b438531e0d456695f34e8dab43850b43d0ece617307982c0084210a164041e1c555c3d0e1e0148083802f65fd2f47c8aa464c859898e3302d20a179d7f562bde389300e2e61669429529d51d30c0798618725b8518c236682186070000021e442c30980a,0x284214a10d0f43e5cb43d0f972c80800904ecafd389d5648a29c2c59c42020436b213903c810ae682b413a06d02e80f4198cc85641b204083c08b602b01580a405202001c12351e538a6829d0adfd0e15c7ba54abd84cc25611b082044c08a16405602b0148087d45baaa858415a70a16ebd82cc15609b042024c0a1c7a4ab8a4b9729ebf774bdd29c2b9e06f06020b012c50a10a942147a4ef9735cdf0a55afe5d218b93a530c03e8bf6bd6cd8adb8529c685407039a16d14e29a2bda740b1147042fa0a2fa1c11808421085a1e87cb9687a1f2a428])]),([0x20408100543287689c0810100a8630ed13408102010c861da2702040202a1843b44d0204040432087689a040408086210ed1320408100c8421da26f],[(0,(0:Int),16,[0x4e33115889c436217107885c04a1cb0028a14a94210a58a942858b142c5ca1269554f3ee78641b21310b2c26018e0160ebc0894087409602b015808299022102190214021c0260e94a0113812c049808e008c8584809602cb6027204e011c021c0215062f0260e8c096023804b011402580af2048d971eb102270c0c3424e0613161c8066841c08441848458081a4289183386b845841849641574a0b0a38a70a46a43a7096296195196275874c749754661507122230429a142c48e11342882509d05d9192044c0a20204483110404110860108a607702491111308982848c06080c91c200c0a5819103820601a68185091428a05040c912301485821304782,0xb002e1cff48d2752708d0b0380c008428431628688310ab0c521623520c0728104b02043502042a7801084210b50db6b52108508541b0c860215570852a5284210dd80dc06602f015809c03e01b00b803c0])]),([0x1],[(0,(0:Int),6,[0x12842108421083682f603701980bc05602700f806c02e00f0138010854b162858a142d0f17878a16874a943942a5a7d280602108421a460a1420485122044611102830a20243092488c212444c0918a54a50a44a43a41a5094c94894496b86084674574274176064a64266484a222844a1222841682])]),([0x1],[(0,(0:Int),2,[0x842850850850a14b8385c1f070a1728434385cb4386a222488a212460818204480c0c18805200c5294292a9229129c25265025c2106102149d05d0990882])]),([0x1],[(0,(0:Int),2,[0x285084343d0e142e0f43c54b97070d84830a1424185088a414914894854814a12892852832e70fc2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r8_ok : checkRowFull 7 [15,23,39,71] [31,63,127,95,47,111,79,55,119,87,103] [8,8,8,6,6,6,6] 2 29 [(0,1),(1,2),(3,4),(4,5),(5,6)] (forbUpTo 21) (RowSpec.neg235 50 (-7:Int) 0 20) [([0xa92031468cc4032628d1948062c51c92548c18a38a4a8983146a494230628c362c2a805162a900c54a3314b12819458a64021528a94c6042a514a65490c0a344b3010a1458965021428a92aa684051524d4d040a32473010994688d6432028d116c862051622d50c40a34628a13013a8c32416027512a2c4804ea24c985009d3070309913a60d160322753988206c45298ad4418c8a5998b10a2814ab316215402962a2a280c51c53144c98a34a6209931466433210628e262c280a51a8c589410a3498b0a8214662a6251328cc34c4826516294509409cc51920a8139895152402731264a2804e62b8c85140a4c4f190aa014b2316240528c962c6a805106fc,0x56350228c94ac6a4051649504814a3451b22881464a36351028b134a06285198658900ca2c8ca89821456195240328a332a286051c85995048a264b1810a1459155120428e41cca6245152394084ca26472010994650d6120328b11aa864051982d8840ca2c85aa1809472460516227628c0a4c24ec314549809d2628993013b143250612761864a2c04e930c8c5809d913030a913b1260625127324c084a24e52944c9409d8919302893992324051272946462a04ea858185089cc8b02920939913250412723264a8204e9234588c09d2459309813898b2431027629a640ac252a338c85180a544f190b2014b35152146029516ca42c805292790858c0a5928,0x41588a5919a0832914b24b310562296456620ca452c555081584a589aa1032894b12d3206512961ac842ac052c2b8c85940a552598823114aa335106422956928426c052cd25484d80a5257290b1814992d32045129323a640a8252cac9881144a55593102a094949e421530296652c426a052c35141098a38692820b1470cc5032628e494a462c51a92908c58a38632810b1468c64021628c98c6042c51c8c989054a38593020a946a326251428d164c0a285194c98d504a30d9302a09462b16254028e158c064a5164b104c94a2c56201929472296230528e252c260a51a2a5914c0a2d14a11829459294130528e14cc042a5198998d448a3452b229014662,0x3093a32606521272c4c062a44e54980c9449d9128b02913b0a51625027344a280a44e58944c1489d851930a813a1a32651027522c0c4824e8c58190849c98b02a10938e1603142271a2c064824ea854581089cd0a8a82113929515420271c2a260844e32544c9009d4899302093a19326410271926462804e9438188c49d1870319093960e05132272a1c0a4624e4c3814c849c70702099138d0e0423127161c086424e8a3458c809cb068a81913948d1523027251a2a6404e3834500c89c6468a118138a8d14320274a164c0624e862c98c409ca459289813918b25310271916482604e0e86ca42013e04208ca0fd04206ca0fb042086c0f7042086a0fc94d0,0x55195140328e22cca8425198598d048a328b31a109456165341228aa2ca684251c85595008a384ab2a101469156120428cc2ac68045192558d080a2b0aa9a011471136540128e126ca82051a84d88410a3289b1a009464936341028c626c4802518a4d89040a2989a920094529352410289c266420851c43994c84a35073218914690e6432128b21ca864251c83594c08a3846b2990145a0d5430228e216ca60251c22d94c40a3485b218094630b6230128c516c462051582d4840ca2985a918094528b52310289c1684206512c2d08c04a2545a1188146a460416227528c084c24e99180c5889d2a30193093b24515062274c8a260c44ea50c901849d2a1918,0x6254128e258c264a51a8b1914c8a329630a919464ac6052328e154c062a51a4a9914c4a32553028994632a6253128b4548462a5194a58540ca3154b12981461a96153028d44cc8a2451a49991484a329331a909471256120528e446c420a51a48d91404a3291b1a809463236250128c546c4a2051588cc8414a390e32a1914691c6132428d138c06485194718508ca324e3021194591c5132428b138a06485154714508ca2a4e2821194531c5143228a538a086451c469950c4a344d3018a14649a6041328c634c48625158694904ca2a4d2820994531a5243128e132ca86051a86588c10a348cb09821465196140328c532c4860518665850c0a2d0ca918214,0x94a935520641294c36820c6452c731440d88a55652101b094a51d420631296594a406c25294b54818c4a4d15988229149a1b310542296368c208a452a6d1841508a4cd62081a914961b410532296358c206a45296b18414c8a4d552101a894951d420531296554c406a2529aa98814c4a4d94a109a814a729621530295338c206845296718410c8a4cce2881a114959c510432295534c40682529a698810c4a4d4d2901a094969a520431295632c42680529c658850c0a4d8ca909a01497195214302964a4a482c51c32940c58a34a4a09831471455120628d28a8240c519514c4818a3921a90831471346142528d268c2a485198d18d508a315a302a1146332,0x1cb549924530472b5264514c11c78e1910243475a34658050d1ce8d1950143471e34648050d1d44e99263404751366458d011d25c99564304759626594d011cc4e992534047595265950c11ca4e992543047293664550c11c70d9912043475934658410d1ce4d195104347562c4d809051cd8b1350241471e2c4cc09051c6cb13320414764a9318950d038a94a6154340e1a3258150d03325496321040e162a54190d033161c3265440c95264c1951038a93216544061a2c41951019262c2653406192a4194d015261c264340519264190d003868b321040616c842ca052c338c85580a550d98832114b1d451046229529a6408c252a474c81904a5969290230,0x759a2c4d59011d568b1256404764b93114d891d9274c1536247649b3014d891db2a4c5436247549d3050d891d526cc04362476c99294498d1d7262c45632474e98b0558c91d3662c056324762b52914d851d3a549201634761b32514d811d3654921063476274c8d91451d899b206451475274c8d95051dc993160154473a64c4c05511cd993120154476172c4d91411dc593161054477162a58d1411dc589963540473562648d5011ccd89913540474c78b1194c91d3172c16532474c5ab0194c91da952960153473a54a50054d1cb952920153476172a518d411d856a926350476156a458d411d25ca946530476954a58414d1ce55294105347695265914c1,0x8cf1d4325104974c989049951db3262312654774c985009951db3261302654766c984409951dd324c43562476ac548d15851dc7261420654769c984c81951dc7161410654769c584c41951da70d1345604765c344915811d8f0d1145604765c2c4919411d8f0b1146504771c2a50d9411d970a9236504763c2a44d9411dd2a51502644774a9314d1891d5aa4c134624755a9300d1891dcaa5252164475aa948c85911dca95150164475aa544c05911d5a951201644772a5294d1851d5a94a234614761b344d51811d86ad1254604761a744551811dc6951510644771a3254d1811d568c9234604],[(2,(50:Int),129,[0xe89ab2c9182932926a536253319298e8f69e6b25a321e1ee9ea9e290e9028e68cabc693c6c315c311b1de9da9d68e28d68c68ba9668f2bc3126b118ab2ab934b53c0b32dc096bc130a2aaa53c233a6c3666231e272e2d2e38ec32d93c4c3a4c2b4c261d07685a81a816b94c32cc329904eb219356905eae2904283e99a9052b0da04a836832bc6a02a82688687a88a87281e88288e822a4b33c2607e86e86686a83a89286282e8568469e3a29cb3a7231d92e56262e261e3f76dd3a35a98599801d02571323332788c745256bc01545e145d1980a8069f365c999ab3c7238ea38cc334c26353c71071e2cf1b1e3a172c96ac9b3481bc661d391e39366a032402,0xc748c06f8bdabd6bc4321ba34c521b322ad229d2acd3a463946364638c335432d4322bc21b922b52e5a34cd334e2d361f6a029fa9fe9f2bc4b263c263913e9368eeaacc196a63a11ea62d122b6191a99112959910a8fa9d193a192d1911691a95aacb225b215ead323a3231b229b21e32192b191b12e906a4b23c360b697e8ea96ab4b21768a69469ae9728c28aa9b29b69aa97a96e96294abc2938a91aa9294939293c1635290fe9d2932a9149d26a914e8b29a69528be9569a2bc613a61366130d330cb30b330ab3c0e18a9428de8d2b0d51ce99a9d299ebc0d294b293c2a2e1ca9c68aea8b93a5131d12e5128b3289b18693a92ab2d11c29be9ba8da8ce89,0xd4f094f094b894ac9478946cf0540634814320508814120500beebdeb5eb2eabeaaea52a16b24e396438e4356434e4324d32bc323c323a323932363235322e322d321d319301bd206f0811f2f9ad4ac0aaeaa7ac47886ae988e388c568c564c558c54cc538c52cc4f0c4e4c4d8c4ccc4b8c4ac0488beab66b3ab12af6ad3124eb969273634b33a3118ad189d189b271e3a66212a0ab90b388b350b318b2d0b2c8b014e2baab9ab7ab6ab4ab3aaaf0e854d854b8545a5496acc589c585c58e44ce24cd44cd24cb44cb24c744c724c057c815e20574815c2c9ac8ac7ac6ae898e498b898d2949a94466ca2acad4d8947294e48ce28cd48cd28cb48cb28ca68c968,0x2f0c45806bc81ae2062c81832bfabcacdad3a0530812420534b09d309b30ad29ab96130dc28eb0cd30b535613c5201a42068c81a220670b8d233522cd2294e293a2936291e01252aca97a89ad948a4b8a89406dc81a62069481a120680815a20484be2b4aaeebf2a9333c53291b30aba5201482a4acb948a1ab1a052481462d348048cb1d23c2d293901472066c819a20528bc54014b2fdac3ab2ad2ac06a8ab0e242b4d128cb2b26019920660a8cd28ad39512d5128b5289d27eb1cb3a4939492e492ac929c924bc24ba24b924b524ad24ab2526249d249b2516018c20628b42b2aa531012029aad538d52ce928e528e328d928d328c728b928b328ad28a728,0x64dcae464c6649664dea786495a04a0b86b6ab6e812920498a1eae19376a06a99937ea6281272e0a061881852061081822f0d09ad004fc813e204f4813c20478811d20444a96a6ea4b4011b2beaf114d4c88caf0d4062481882061c81542acc86478ccc864b872c8e2c8b8c8d8c89cc80468b068115206b481ac206ac8177205d881752055c8151204508136204d48137204d081132a8aa8a80448a46ab2a356817a205e48178205cc81722e4c40604a82ad292a29292901742aaa4feaffaa6a4c6a496a478a404408133204c8a2aa0e949b362901b2206c481b02067c819e2067481592054cb0d93c643c3a01bb206e881b9206d881b52c2e806d081b328dac,0xb22d516a432ca719668b3218e33933054092022a042a04005442f0ee4a04608116204ec813a204e481382f4aa9a92a046481172b8aa4a8bad6acfa6cb00640818f20638817d205f0817b2055881522cca9ca06a481a82069c81942064c81922056c81502eeaf1aeba04c48130204bc812e2f3af2aefaedaecaf0a9ea99a8fa88aeaac5ab5ae9af124928c06e081972065881952064481582d8ad1a98d8051081452d530d3300470ac2ab6ba2816e20588b8e812d204b0812b204a8b9eb9ab96a76a3ab8a816d205b0816b205848160205c48170205bc816520590816320554b4990180205fc817e2059c81662aaac94405a88169205a0814f25a64aa649a64d4,0x43e8082850b43850a0008766d01680a870a1428d35c6c5a02d01680b4051468ac8285d01680b405a0a8a57852ad3850a1500142e80b40543d0f43858b16c05a02d01680b405a020034383050b2020ba223a38a0a545b4678d1b56aa002858b142e8082850a1687a1e878b16870a142850ba02d01680800d0ccd202d210e285d428a9a80a1e2c58a142e8082c50a1687a1c2d0f14285a1c2e8080010b8c16414347542e233cbf9a8090150f142850a162c50b43d0f4385a1c0010aac1428500041730d2fd001428500002ab052c50508b882e551e3f4ac50e1963a1e000105bc5fa9434658e4781bd25432658e278d0c596385e31cc5993a45869592728e52cc3,0x20ce88bb124e02d0f438500044d700020b188813404142ec6a29b482800a1687a1e870a1687a1e870a142850a16404142e808007121c14285d01680b405a020ba02d016808001051c16404148810881088136756bd0f43911220088134056020a1687a1c2d0f142d0f43850a162850a14285a1c2850a17405a02d01680b405a02d01001a213828522042204d2900020e99cf0b4ba002d0f43d0f142854b43d0e142850a142c5a1f405a02d01680b40400687b60b43850a142e80b405a02d09253df680100c388913eb931311a3801740543c5a1e870a14285a1e870a14285d01680b405a02d0100061d5a870b43850a142e80b405a02dfd0ba88910ef2b1501,0xa1740543d0fa020a14005168c148810280220bf800304ec80a1e87a1c280062ebb404006828ed01682b405a020a4408148813404142ec4888102ab4a874050e16870b43850a4409a02d0165a1c2e0f43e5a1c216c05a02d01680800d14fd478ba8a14000835e4a38d01050a1740543850b43e80b404142d0e4408142d0e00089ee0a001845e22fc4050e0008a0ea1e870b438529c2850ba02d01680b415a02d01001a089b4e52020a440844084409ae20a2b2221cca800b4385d01680b40414001135c14285d01000a10f8883028aa9a70a003802a1c2868700004cf50e16870a175e5378cab4241f231c28d4a9800044e3680800d051da02d0145d016808291,0x461b000a0fb95e5a9a0a4408445857405a4229e6911220240517c05202001460b50e1787a1ce1400082bed0168086043320adfa31c50fa02a1c28500041db6daa28c09645aa2c72ac05d0168082800249d930e02d0e4408142e80b4041400517fc4409a020a4409a022204000427b0b28b74050e142d0e142910200122fda87a1e8f0a142cdd51001a0a382e80b405a0ad01680829102052204d01050ba62155116a051a80a1e878b43d0e168700046a3050a142850ba02d01680800d046c46f844a9350143d0f43f0f43d0e142d0e0028b66a1e87a1c2850a142e80800d066c282c9dc95e0e753263405a02d0168082910200022dfb405a0200042cb251c050,0x9a02d591102110e1102050ba02d01680b474440814af22244050e142850a14881088108813405a022204d010012329a870a440967800211f8001055cb4640cc435228f1516195612d0f4020a942a5002464350e142d0e142e80b405e2a1450c09280020e787155ba34c050a142d0e0028c9e0ba022204d01680a29102001a1bd918e287a1c2e80800d196c4408148813405a020a142910200221a9900440943850b43850a44080018cbe22042204a3c6d0f1687d0151e14d729f415a02d01050a44081401105ad43e80b404176e46ca6dd004408142850a4409a022204d0168082e80a87a1c2d0e0018c3e220c00141ef110250fa02d010faacf9adba0287001,0x444182a2a1ca72214223c73ca8d2a15c4641804408142850a44084409a02d01680b40543d0e1687000c71b110a68080010a2c174044729438b2a97a3cea02870a16870a1400f1c0d438e88a910268086e808881000106fdb5aa1c2b4290143d0e142d0e0008dd600142970c4b5359f8dd0169288830af22244040082850b43801236b82801a0bd9d85a8ffd017ae91a5438b8a8f3a8c700008db600043ef229c0500046d7680b40543d0e00286a6285268b0c6b143e80a870004ab3262c052204a1f40414881088108810285d0150fa02d01052204d0105004468f110200221e990143d0e140031a1c4409438da1e870a16870a000838ed01680a8717950e45c,0x4184408440943d0e1453414285ba5bd5663206011021102050a142910211021102110211021102680b405a02d01680b405a02003478b000a13bac75c90d220cd05115e50e14f76619191661a1a34f0001109cc15e722e4d01680b404ea2222422040a17405a02d0168ca8722040a57910a51ecc620c0a1c2d0f43850b43c00b4040068eb60b43d0fa02d01001a0e98230a0b65a181020828522042204d011102115e50e14f7463800042930522042204d016e6a87a1c28c890e600011dcc4409439102000214ba870004167232ca980a140052ddc8b31439102680800d2d9c8022040a0008eded01680a870ab9a004410f050a17405a02d016be82e80888105a,0x2204220422040a14285d01680b40444084409a02d01680b405a020b43850b43850a4408006902e3dc883088508b90011071d43850a44084429439eeae21a4409a02220ca1e870a29a0a142baf4ba03405a02a1c285a1c285220400247e3680b405a0a22048a440830223ac0a1758446b94b8522042204d01680a871751132050a44084409a0222042204a1e870a579136050a16e96e166a000111f4c1454444b9a02d01682b4044409a02d096808881029102680b40414285220400441c74d3ba02d6d1df4b850a44084])]),([0x19394620a6231728c114c062e51482948c5ca24452018b9460866021728a20aa240e5124150481ca3101b10839446033210728c416620ce452888d4419c8a504b210b38149213410572292416620ae45286918415c8a48869902b894908e321570294642c42ae0522434c811c4a5052302939460a26051728c442c4a0e5184858541ca304a302139460926041728a114a062e51882588c1ca2904a9183945109513072892128260e5142194085ca2901a908394488e321470294622c428e0524c454851c0a5088b0a039451115140728a118a064e5122190085ca2908a920394701083b284a81083a304a410839b04981083a2849410839a848c1083a184b56,0xa12e64208188502b932020611542067129421a640ce25284954819c4a484b210ab8148a0b310472294328c208e45246514411c8a45452101b894a28a620371292514a406e2528c25884dc0a4984a909b814a1146142728a228a284e5142514109ca31093120b9450925041728c118c064e51282908c5ca3084b0983944a094230728890c6042e5184158481ca228298903944a034210728c426820ce4528238c859c0a5053290b38149115420571294544c40ae2528a498811c4a494929023894898c410372294318c206e4524631440dc8a4584a109b814a1246152728c444c4a2e5148494905ca3108b120394610c6132728a218a264e51243104c9ca24462,0x4892a38239093222a8e08ea2488b083a23989222a20e88e324889883a238a9222420e88e2a44491a3823a8910ac48e08e62441a8a3823a22c18ac6e48e88706231b923a20e182c6e48e88346031b923a60c14c24e68e5830528939a38e0c14824e68e1a30500939a3a12a14ac6e28e842c5031b8a3a52214ca6e28e44685229b8a3a51214c86e28e544852a1b8a3a50c14c42e68e54305290b9a38d0c14842e68e182c5010b9a3a50a12c02e68e1c284900b9a38d0a0c846e28e82a44ab1b823a099128c6e08e52284a8839a38c890a846e08e2c181a0138a3870606604e28e86181b1038a3a24282ec4208148890ba9082060a122e0ca88128488ba10820460,0x422cae08ec2910b103aa398a442840ea8e529109903aa3922342240ea8ec2890b083aa398a242820ea8e528909883aa3b0a122c8ae08e528489a2b82392a12248ae08e468488a2b823b0a112c6ae08e62842a12b82394a10a64ae08ec2841b0ab82398a10682ae08ea85093093a239a1424a24e88e385091893a238a940c028e48e2c5028823923a13224ac8e28e846891b238a3a113240c8e28e446891aa38a3a91222c02e88e64488a80ba238d1222602e88e2c488900ba23a91214c68e28e6448529a38a38b1214468e28e2648501a38a38d120c648e28ea4481b0238a38b1206408e28e82c48ab23823a099226c8e08ea2848b2a38239099226a8e08e425,0x609b3923a2c41806ce48ea910320b3923a94282802ec8e950a0980bb23a34282402ec8ec508529b38a3a1c20c04ce28ec5081a8338a3a9420680ce28ec3120a903b23a8c482840ec8e931209903b23a24382240ec8ec3048aa33823a4c12268ce08e8b0489233823a1c12228ce08e88d12232b923a22c486cae48ec89113093aa39a2444824ea8e4a9110093aa3b22442c04ea8e68910a013aa3962442604ea8e4c9108813aa393242828ae48e5890318ab9239a240a80ae48ec4890b00baa3992242802ea8e54890980baa3932242402ea8ec488531ab8a399221486ae28e4c88511ab8a391a21406ae28e54881982b8a393220640ae28e82950932b823a0a3,0xc91212893b23aa4484824ec8e8b1210093b23b24482a04ec8ea9120a013b23a64482604ec8e8d1208813b23aa44488ace48e991121ab3923a344482ace48e8b11202b3923a6442868ce48ec910629b3923aa441886ce48e8d10],[(0,(0:Int),125,[0xe219c0a9a3954a4d1449268d058f114d114a948b04c68c44dce1344ad6caa30da3a2a3c61190e2a511d341cb434b214a52cb23a4a260e2a6b33975ab9d54e3e2d070d1c4680ddb0b063cc3d648a34191b6864782a64704370384c513472d8688c588651e58da73964c40e09a3245785c5464e70b2263212ebe391ab498b19294c944878d84c467019d4e19396938ea06da1f1e3b01b8e1a8781a384a384649e70d815261a6a56d930cc55053ac6780be6a5b17592f0c560c988a530b114c96068c8c5ca9e7c46256393083ad8dc8e4cb8b1e0c67993140fa95c4bea8f527cd2e4d62b35c5844daf01a4c5464a449641cc68cc2951380b30f353995c96c43a002,0xca31442d442c442225221a2219221505284e82280eb43303683281e812bf624232422c42213464424e74585649384614291462a24b7068142938701454144c1464b278aa74226c226a2268226422622254224c2243222322111a62702a48243408501508d07d055760ac8357238462405d02d00506e435ba9a1a1a0b14888b01d413403586e055112a5814c8e4a2e08ae055cf8262ad782503dbc361c3518551a219a2d1a0986b5b094b08c63ab11a5c6261b262b5a73c748a918a4a98468c85925189ed27a85e741a2c0e20a51d2c288a315c2944223a2239223822322231222a222923213858424c4211166ecd7ab4e7dc169a2e1b2901990768746cd403f3,0x5a3d4e3431261938729f9c868f028e42865c961413142c1471381c2c03e693929b82d342c32381c291c2a1a1a1a39112e1125111c1116111511129114a41219121612150bf31b125a23a9814e0744c500f483a6d263a1a3412261221921612119207525745542f519d09adc4a4d4c444708c382da2ca18af01407ac178416441584154131617d1750cd34544a683a623126590a74d44c745a704a7052706cd4381c38160bb784938193826380e381a3823196ba0a9639b118b034a5ac3b61b20d163c6c231a16729468a8991794d2f8c4649478e247d53cbd289ab9d3cdce6cf217158a8a214d070d24c27487949ab20a06e86a9a0a072b84e34442544384d28,0x1c391a3a053205250314a946942b4b81c161c1339383638353830b83d392cb81c1538b828ba3a32325bc231c229c2194ade164e2a8e130e170e168e058f190d150d0f0d08cd038d03487cacc53e3d389cb89b349d391e2e161e0e9c8c8981e1f1a8d8a84bc8755cac292a13b23f9c25492e0070ca724d704c705958683a5c3423267412721270126c126a12641262125a12541252124a1245123812341232122c1223121c121a1245c55a95694e8fe8fa8d290a9c8a102b88a3a0a188a2c8a1068deb60a348a0cab54424c430d2394434c40e150c289288a87685a87ab1b8192c3a211e2110951d212a21315915213c2124b40a68a289e88688287e8569a2932,0x4a1a0a188a184a168a148a128a124a114a0e8a0e0a0c8a0c4a0a8a0a4a068a050691b51bac6545d45544d44522d22521d1ed1e51ad18d5c645470516858665258313854323432782c7424712470246c24692464246124582449243c243924342431242924721c6a1c121c121623e51330f50d50b5094f74f54f348b50cef4d05492648461845984548451844c844984427842724270426842624258425242384232421c0ec518a885c3ac2ac1abfabeabda49a48a47a36a33ac4e462b0e0a4e888d088c288b888b288b088a288988892888c88628858884464c4382dcccc682a7ea513308520ba20b420951c932a050e051493315a151934052c0521b12e2925,0x69d29ce9368d7385d1a131290984e12498279836899619b3d53b52352151f51d51b5a90995c96908735490877571088d5a8c8a4609850cf4cd4cb4c94bb4b94b74b5497588c970507050ff4fd4fb4f94bf4bd5ca89a8d9495475455434c34c141a1b0b89ce05864d44cc428f018c0a63a62a59a58a57a54ac22892b07828e4d0a8c8d274b444a44474448234b8ab7ab6ab5a78a77a7844384483a82a81a80a72a71a70a6fa4ca78c8b05813a8ba44d295946cb7536d3656c64686a705c7248714861485a4859485848524851484a484948384831480766e2423243a0e0a33655635615575555535498951c9b1a961a965a145911561312948c9e0a1c4a1a8a1a,0xe24b0117023b0e222c001612f8ba3121612c2312214c498470059800602cc003016600180b3000c059800602cc0635e145861583a04a1ce81287a1d1812873a049a04a1e87010427f17024d024d021702009a0eb8017044d439172001608b910e44c5902590259025902590259622e38a9464696e8d68567d6755e55dd5d55cd27d69a47298719878883c2a077722b1eb1ab169ae9aa9a69a2b8c42cc433381e0d336b32b2eb2aad2aceb96a0e6a1750b68574303d349a290d128d0b0d0709b1288871752b4eb4ab26b1292a8eabc7424ba2beabaab6ab2a72a6ea6aa6693ab2b821a110932a2a9ea9aa96a62a5ea5aba493821362122a1256a52a4ea4a9da9d,0xe14b215809d992c04ec088c09642b01580a9830b9311851d8b2c251c3960ab01170a249c23025bcac0543a336176a58091951d81298d2c54bc288c285c08b22c332c2f66173617321712231658c954586559a2cc8638ce31cb182f5c46044d18b79270c71850c196381e41c016600180b3000c059800602cc003016600180b3018d781382e042e04a6048e04b01580ac04bc09602b01580ac048c09602b0117024702580a98123812c045c08ec094c094c09602b013b02580918129811d810b811d811d81005f0a3cec09602b01580ac05602460400ec1d723022f023b020016081ac056025e044604a6045edc5e047604b2d233a580ad548c08ec088c696028,0x8c18bc185c091c085c18ec09612a6045e042e04639927321e64581602008c2f33b0217022f12472e002e0e19d812c85762b01580ac048c596225e4c2e94b01580978517851d8f2c05602b01582918d2c051c58ec99612a604b01172e23023b1258491810b8d29830b811621aa52522c7542ea83d51700017082c5f88ec09602b01580ac05602b8d47024716580ac648c285c88ec3960a8e04b19580978123812d045c791c094c2961aa60c63b217641ec8580ec096022e04002c1ff3bfa580ac045e4947bb26170a590ac045c08bc496622e3cb091706232a58c94f245e487c91604702002e185ac0543d0f602b1500160ebb5810bff0b812c0560246f476145,0x29263b06530e2312110e3b06110e17063b0611062f0650e4408a428ec485c888c185c285c085c094c391c194c094c385c196022e0447d80601d02580a9f4624a1c005076cec09602b01530a586a872f74b011d023b02170a5828b832c0560ab2158a889d29812c048c79602b052f2a57f60a7604b095809d830b8d2c151c19602b0123021d1a530258694810b832c054c1844196028e04a3e3812c254c08bc18c7622ec43d88b02c056022e04b01580ac0400585de2e045e04b2100160f1a3812c0560a46148e042f7c46044604b0d2336580ac44bd1960ab0d580ac154c085c59612b25584ac34ec185c0962ab05530a5808b810b8f2c14ec094c08bc085c28,0xe04760446042e04005c1f717022302580ac057c27674b095968b9f2c44ed4964a2e147644b05586ac048d396022e045e147614b0158091812c04ec0960276048e0446044bf006058091812c04ec09602760422045e04005c2ff3b026b0e11222f26000a0d38b812c04ec08a8a5f1cb013b0250eec085c085c6947d8aac35612b0158c9d952c04a4185c085c596025204a3dd85238b26852c148c89602a61c8e0c7624b01291a350258091812b7a1ec548c085c088c38740943c102530e41022f021d0623f4030287a1ec0543d0e00285de2e04a1d481119f000b06fcec08ec08ec09041947a302412a35a25809d8723812cb543c706580ac1568a2e04a604b19,0x2c75602b2153165829783287460cb052906110a11022f021106258c580ac0400586562e04002c25300a608dac948e59622472c4604762ca9c883297a3c881118113861d810bf9118535812e94d408ec085d78eca8ec08bc096322e24b193b022f4a17022302530e230a17025848b810b8111810b8111ee01808c19612465c008c1db2fda3b023b022f123b065809d812d2568ab195889185119129a51d8f2c345c18ed188c2962a8e2cb053c2c07d80e047025808b811d81002f0c8cbc4966a008c1b358091810b81119d002304ad602768c5e142e048eecb05580ac04ed1964a462446042e0cb01231617065849d812c249631602b012302580ac0400b861e5,0x31c0d2c0561a7c2c3424b112d280c7614b01586960d0b81129402230659caca450189809012b013b123dc1b7836706be0d5c1a78347067e0cdc1978327063e0c5c187836e0580918100170cdd602b0158097850b95006b075d6025e142e645e0cbad5849d932c8566ab2953f622b01582ac34ecb964ab013b0a3b2e584ac045c488c78ec685c085c288c08ec09602b0517065809d83118512fc018143d0f602007432f5808e872c0400583f6b0d29322f3e3ba61132582ac24bcf85c288c088c095fd82ac247458444963ab09294a11465829d91178f11f6161c0702c05602005c32b3b025809dc1000b060c8dc801782465e34b1dd8d2cc560ab195928b89,0x62246042e0446046ba24f448e889d10fa217441e88d8ce255c4a38937124e245c48789360580b87b014f0270fc3c5001c34370e8c09602a6048e04a604b013b023b020106007a29a4919b1d910053059d60236047604b21580ac256022e24b057de6d246042e14361c560466148b61a3e44bb642b013b3617021306430a594ba7a60cb154d5e04760ce5cb812c04fc094c69c3af022b42584978b2c148c19e0a8e0446048abc48c7826f04be093c11f822f043e09b017812c045c08a4088c08bc096027604b01580ac0560276047604002c32f2302580ac05602abe13448a002c16b59296f80558093031d8721e54b97065829ed82ac6561ab2d5928b8517811,0x15809d812981298129812981298123812872e042204ee048204a604a1dd812981287760476047604026c00301061c9ac045df801d8416a63c76043a64b79580ac148cb85c796123a04bfd5347458a45874188c0943d82ac0560aa5da8514a11181118711832e73a1c6a44460cb0d3b0231e11bc22f844f087e10bc20f846c0b012f02170258097812c05602b013b0253023b022302580ac05602b011702580ac051c08011868e5e042e048e04b013b023b020106037801706dd60246042e047604b015809d81009b000c04d80562e8cb091782530e174258291892d9560a5e24b39170e588ac148c08bc59612b05231258c9d812c851c588c194c591c088c09,0x62a7664b491716320a00460cb9181009b000d62246044654bf12f061112471e3b0a59ead249bd82a004a409602a64ce0135d64106231a586ac14e7289e511ca179427282e503ca1b02c04a408a40940096025e0452043a0428044b6022204b01580a80123812c054c09602b0158091812381287b01580ac0494098000cec088c08ec0895181238100260fbc50085c090027604a604b014702380211023b023b020106001ac44005843e2e04b013b020136001809b000c8c088cc8a41947c7162c362c48b83118512a9062aaad2562a2511406596acf4b69af118f2c254c18e7249e491c9179227242e483c91b0118123812c05602b01580ac05602b0150f602b,0xb02c0564090409602b01580ac056025e048e048e04a604a604a1e38111812c05602b015f02470217023b023b025302007627d9a8129812c047408a408740804d8006026c0035a28ea5000b06cca40934094c08ec0804d800676047604026c00301060018ba72c94aa246cc52145eb44644b3d112a231a1102230a59a9d871d91088317892c04ec788ca8746962a5e04b0d23062f0235d227a447484e907d20ba40f486c0e01580ac0480096028804a1dd810a010b812c05602b01230253024702580ac051c094c09602b011d022570048e04a604b01200250e5c091c096028e04b013b023b023b023b020136001809b000c04d8006020c46f5808a0120044429,0x5c1253d9b4e1a3c12f824f043e08f00343e0f83e0f9707c1f07ca0008a86cc5561887578be2e1f4be5cb5f20d90528421ca18b372f3db8ea385072e5cb802c0152ca37051652b2f55fae5fc02e01700b805c02e09120a2e1e3430122c312c8380a8409ac088c091498117810d8129810039147d202b0139022f025809c811d8134048c08bc09202b0153022d02530253025968bad0bbb0ab92c25f6a3204b01580ac04ec091c09240894091c08ec09602b251756698bcf45d29602760476047604026c00301360018083004c8cb85cc9612b01586ac55632026c0077df22a14d4716496ac151cc9602b252306588ac054c38e7229e451c8979127222e443c89,0xe74180268226232c8211d6a5bea9a228cbbec24d7448e889d10ba222124c034044a74096022e042e044b43a9021d0229021d022302000a2c596010e81287e0150f61225950f632b015deaaa5451d0251e7559742a1e872e0c220cb015be8005057d6ba6a1c2e04002c10f1122110a1d125cf43a22c230200162cda87001426f000a0a5ad54002840e467c22044258001459f000a0e7ac25722b014008e810017090c0040336419891738a57148e28dc5138a17141e28f8010842108707c1f2e5c1c00315bd1aa162854b56876a11a4e0f9780000c18214210e5a1f074b8784d7c0d618910494d15ec3972e5c01600a814182c0114aa5eaeef805c02e01700b8,0x97580ac0400582ce001410735d0a7a147424e847d08ba10f426c0b0150f43a902290229021d022902290229021d0200162eb8e810e810e812681238123812081287a7da852c0543a302000a12ba872e0cb011d0250e8c08aeaadec14b5ab552a495b48c0966abdd5348c1963d86ae7222452645204a3c88110143d0f43a90229021d021d022902003a2eb8b81287b052d4a8f00141b750f43d0f43d8088810e832c04b00943ab0a87a1ce83268528f00141231132110e2a88a050e812a72f5cafeb7227c2e24b3ce871421911739247244e485c9090936050e5c08a408a40844087408a40800b8b66a1cb81287223c005c25350e44085c0961ab052c8a50f43d,0x80948310143d80a87a1d48114810e810e81148114810e810e81001118ed3408440961a4a00284769ac422cc2e04a3d644467943d1f439d021d021d024d0641362ba888f0a0508c52f7a3dadfeaa2520c679147222e443c88f012a522044604a1cb81118108810a012c047408740850085c08a409602004460350f43d4eac223b4001413b20021d021d024d024d024106200258092ab2801404ad34285c7961a23845b622521c2264b2150e748957d5f62ab3d48508a9108e0005182c9518128700141531dba2c2a87571000a0978bf916de896919e222c000a30bac04005852e2e04008c1a357e0088306b7ee145c48893143cd0229024d0250e00e914600141,0xa049abc5991136182e1de580943d0f439d022602290229022842410b075a50d3bd5d8caed848d871ad4f9fda6948128f2e144b47d4e4408c7886f10be213c41f882f103e21b0287a1d181148114810e811481148114810e8100351a6c8c394f800a13fa873a043a049a049a0482045204b155aea8752043a049a043a0422049a0482e45954d021102113a51f74a9a043a4452b4a3c8950b8b0b8329f2e7c5204b5ce810e8f2c04a41880a1e873a045204460452043a0452045204008c67750f43d6e00b821e3a0c3a043a04833c5b517021d021d024d024d02410a50f43dde8e81268126cf2d79a0ca1cb8b26832af5bd54f60252b4a3c8a10b8d2ce4a52947d,0x800a067c0f24a36871a18a1a1f070f5cf51ae8104108429707c1e87c1f0c4a7cd24d022a2312ba1d3e67e01700b805c02e01704825b84b74610d104848b105051adc6138c17181e30f801084383e0f972e0e0008dd60e2e14e4a81041ca18e00800c047c292c0d258b16870a1434b854e5c990707cb802cbb69056baae09208421cb83d0f43ddf27cd04d7bc55734be30ce7e01700b805c02e01706b1ed4614327483e905d207a41e04983320e027408440844086c08bc0814a81287ca7408640880090023a042e042e04520422040a0258d364604e1d286873a049a049a049a04829c66b12e64b23692b8a873a044604a1e872004a1d18114812873a043a049,0xc010707c1f07c1f2e0f83e0f940011d5d1db80aa21000009db3972d74b0051687eb10e2f972e00b2b5812c0d610b02417e99e0c2084214b43e0f83edf73964b5c5f95dde7e01700b805c02e0170492a5f8bddafc344820c008421421707c1f2e5c1f07ca0000e264b3c05616b2e5cb802c01600])]),([0x10108765440c040221d94d02808088754340c040121d949028040487532409010121d0c903010028765140a0100a1d4c50240402874314088080a1cc8503010018765040a010061d4c1024040187430408808061cc81022010187310408404061c84102c1424305062a1943d518244250885542087aa281828488521087389981828488421087389a12214181542187089911214181432187089b05088c1214a8630f5460a1098222550c21ea8848890a0550ca1c22684889060550c61c2278284860a0c32a1c3d51418182842a10c39c4d418142442a08439c4e4283024432a0439c4d418182442a10439c4e4283028432a0c39c4e4283030432a1439c4d92,0x122010e1d1d20404623874728101148e1d1c6040442387470a101048e1d1c24404023874748100984e1d1ca0402513874718100904e1d1c30402213874709100804e1d1d20401603874728100540e1d1c6040140387470c100480e1d1c2840110387474410118ca1d1c9040453287471410110ca1d1c203041328747080a100ca1d1d0840263187472210094c61d1c484024318747080c088c61d1c2018203187474204058061d1c8810150187471204050061d1c2810130187470604048061d1d0440163087472110054c21d1c444014308747080a048c21d1c2018113087474104058421d1c8410151087471104050421d1c2410131087470504048421d1d,0x7aa30448491106a8210f54304888a120d0c421ea92140c142194861ce27050911205950e1c227050890a0594ca1c22705089060594c61c2270448506058c861c2268448506054c861c227420204568747488080d5a1d1d12020256874742808055a1d1d0602005687474060811961d1d0142036587474048809961d1d0112016587474042801961d1d8100863587473040210d61d1c9100823587472240204d61d1c8500803587475020218d21d1cc080853487471420208d21d1c4880813487471120200d21d1d21008653874720302114e1d1c80608253874720142054e1d1c80488053874748202190e1d1ca0808543874710182090e1d1c4050814387471,0x305084c1112654187aa60a10582122ca810f54a122118242990c61ea98244150844b29843d51424443050653218],[(0,(-7:Int),387,[0x282429b82c3a218810982c24192c23181298300d180b213028031805140638120a123c1624a4320a11982298262a3c0c2621300e20b420b8350c190c28221c06280b0c0b20b22232280e0a8820b024b826281c1511183814037311c1a5e14029403144c1292084d17049052090c0875b2a8424884e060388c2089cc268282623106c7221284954501a41244462611422224442613043305110161024d5288130832182111213126382908249c20a203f30909c050a4d128c944504b1262049cb1102432680a541422282a326230780622382938641041583210580a61104a38521241e6c03121a2222212c1a083c052a082129222931083c063403222a03e602,0x9c8c050343424e15023c98267026704652a264c207b694c384a384c23382c3c30f3c2203a49a1c0d243a26291c0b2c0e249410f38028c8c08b5a484d05425ac570582a70c461a84a9206c6c232c2528aa28232c22389a0d19390919881612380803700c44346c12481c280660065432181c111841d69490a0a1c19384921b80a0823eb6160e071c4601f1b4e49868a8e4c0c488602430e04462285288c5500bac86252186832300622e540b091124a80a112cac2c3922090a6b46514660504960b0539c054a2a0e03472308a20700c58440faf0684974782a382c5230294831580ab5a0a1a3124131e09180d24ac30132a18109c0c0d2109264a1a3219311318,0xe71113c8c2c0c2e392b4e523058243014501494e0b0684228e094a290c490c8442228b044a450c3604468d114c988d184f18854240f094a6649386103021658ac0a030a098e9a8b564b0a4e02c60588aa09504d570e5a05c9ae3a1a883c092c06161a243c304329282a28380112120d0131011b4a7812e65342509312824b4360a252c0672279d470c2309460b2f0343085c839514bc0c9a2196131a2a1a0b070d098701adc56006ce02c504a292864625360687819245610163ca0b1194184a0d00948084808c80930084719034b024d8e8822818248230b864e1cb430582403742bbc2918b093181c019c028e129d2c9aac82030e02930c9a0e0a0f1805143,0x1e05986910a08a0a9e3710d41e229321138c14621a2c95189c0a9a2f0d0896611921162498b9dd51a1b0909f9a620f038e088ed21a120e98a219049c2110b58490b0a8e0906214c4d0688886c0c8a0cd7a80a2114211c34013191250132010e0116012a11002940e293922111caa36113622283424061c111c2b24b2309a309c1c1c348c2528304c24a23049304a2c1b20b1066a275c960c4280ace8e7c52294a13725b52ba93e580c2330300c242432022a023c1b3d1e1529341e18250d1118132c213843341d3c4b34dc24c210e28b1b104e530c9cd0425a7848644c2403d5d092263a8c92131c0606031a170880919f6024421858022a0278026c624a6248,0x29c171c0e131c9d0d18580c8c929c8e1484693058c86870b8e0c470683824e06c0d086441aaa79e098a490138aa487848242212b5c2404ca0cd28382bc8c9521614922c142c13090b236a487094c914892469a23052df19018e992a262c0bd4c93191c14eae35a3caad58eb0f965c9ce4cf216159c9ae47723790708dd725b16d696c6845bb211920b180e15941258128a144112410e010a410701064114161e011c010d010c41130118410b011c860601198c121b1219980d9b011f0103f43d43b43943742b4294274254234034805880c880d1823182c94591105139c172d1d2d1c321f3d0c8b172c971c18980179d4e0c2d0704ce444fc68a161a1c450e0f,0xa387a3262127a78722861b47a6c14c53e392911209829160c95191b2c870914209651149898e818ec1e0e9d0c9c0e904a070893540e4e01e93838e068f048e420a250d270aae0902cb4a496a0a8485da684890f4a6a0c864c4c45cae490a908d350498ea124285a72b4c06746546346145f4494474454434414055a310c154d493488a459e428e4d8e4697051803180a1a19180e8c17050094948a13164196428b74b54b35a599b981a1308c892428c418a09184e904e8af4bf4a0d0c1312599a150a4a88860e009a031290944606008b144458d0496508cc49a488ac895009b1084848846145e0c352a20e591a250e1898a8121514189eb61518148e1a050a1,0xe4e84ca4ba4aa49a48a42a41a40a3fa3ea0ea0ca09a05a2038202c4640c4404a40c24098408a40c8404c4054405840944092402034524047a46a45a44a43a3da3ca3ba3aa39a0ba08a04ac114a41038a37a36a35a34a29a28a27a26a25a07a03ad5a4f1b0f1a8b130f1a4e5982ea2da2ca2ba2aa1aa19a18a17a16ac5446450c484e05838283228a44463a5828b250c504e14462ac110a04cf310d0acd3904424b328d9a4f078b904e368e3a8e544a944f570f5d0e9c8f598e944d368858e22838466846300c5270684824426178385a785658643046705669742f568586972637259727262585c24142412602278265870448468747af272e27938708c71507,0xca28c322c00021b7914586158080001b7922600000c3ca18c8b6388e24c06a0dc84d446a1330da6318463c4604425c460446bcb7517d2201c5e045860580a142850b952a50a54b9428707cb152a54b43850a14216286805402a01500a005402a01500a80500200001cb042942e5001012b2508ea82945e42d21690416428a0452504163861498594c73bf26b8506d4bf83e9f83c541184310640c06808c8054809480d0805880708098804c80c880a880c480b08068806480a48078c168c178d58c56a55a54a53a52a51a50a4fa4ea4da10a0fa0da0aa06a4058404c4038a280407040549280a4809880a88094808c8086808a8040347250caa06aa0c6a0c8f0,0x529dcac7886f10be213c41f882f103e21b000020f6c14a1ba5a917943a824924a148508ac83efaa229d052ba9f8d2f59449455ad7c5db92de776086843221891738a57148e28dc5138a17141e2958000202664a151866929d9a0fa055050a9720aa06d2fe97985082694f2f57d1513b33decce67b3c9239217241e4849dae893d123a227443e885d107a25e0050852843559421460500216113281b4137d250a94288a33c2851b50dc8ac7e75379ddce255c4a38937124e245c4878936065c1f2e5ca972e5ca172e54a16870e54b9528002125b070852a50008137042947551424fa061042841649528d480010b2c922c886384e00020a8c0d20650d480040b1,0xb811d8d2d056026426a235099651c7304e603cc0b002852a5087284383a50c0080010b3c8e0645e20b152f0a5996092a39a3aa6b95fe28d1650a8929ced429dbc29be9547b9f2c6e5f8551caf2dc3987142a8e9ba4ff7694fd52f5aeb856ba44f488e909d20fa417481e90d81942142942a54a0000576460008216ca1429428728315a0fac926824ba26d25ca3526f86219bd28a296733c144dfa7e14ddaf47f52f0aa3a5141457b239d8795ce251c493890f1212ae7229e451c8979127222e443c8af00214383850a5000828f458a1ca42800008992853f0c609271a4fa35935095145641841468a0832fa54a9428229d74a0b23fe4f44127e8ba8bca797d2e,0x2580978111811d870b852c048c18c7846f08be113c217841f0908c1b0002310cc8cf97f085c197125e1c8e0cb496b6e3b6e2febcf943d0f622b492026171e42aac74ec687428ec487458ec085c096722e8c2e045e14761c2e048e047604461c5e04b0551f6124634b155829ce251c4938918121e249814c08ec0801d863ea604002c20b6b262f6a230e235e3540b43a14b01174a1a623b3617022ef612b3dd8711911544447844f89928699897c169d830a153804922c886253145890d309c00460afac145f097224604b5d17d22306147e11022a48b812c4448a2a158688a90b892d45acb8753890b3062df45e6978a464cb0d0b0918f287b195b09d8d1da90,0x1bf2d2a55278a551ca857a92fe2f37d287ae5bffb955f49ded396f142a55a90ddcaf8888f105e207c444304c000001570faa3f44924eac23a48a6b37b58a9d08ba10f424260865f1051e08bc10f828261380100001330f88003042c0a247d634a0aad6d5297e172342a4f34295476a95ea7ebfa3772fe559f5e5899eb46bb483808900020e99164ca22a913000083860f91ee5fa48b221894c5162434c27000102ee09ff53d2e193e017c01f8180c0f0000b0c6d7c08011822e008c1273b6a236258eac156925ee4470ca61cb6d58091bd0b8d2c04bc58749960a4604b0d5869d8711850b8511932c04ec588c09612460476245e045e04b01170a1702230e2f1,0x10ba30bd12981178108812c05538106041918717af0083015c4438ad2b0159cad048c18bd4953970e586918511810b9f239315845c1957d90ac748cd963ae22c22047614223c5e04b1158494872874858008c14f2f5a230a173a1752230253725aa91812cb4bc588c788c1965a763c468cf411106582ac74ec28bcc8bc096024a1923161a1a13b28af57744618b6500760818dd91d8b0b9d2cb56024c18b115baa744c7501ea0a0c0b000000c1c19a0000246669ba0b0ca735948295641861d6116d28ea78777a1cc7f1c214b58bdea56a93c52a5abc2752bd4fc2aaf0d2caed52c4bfda9bc52fdfb962a8f972c5e956af812c0251c4938918121e24b8010000,0x811d8111851af8e042e046c2250448e88a1113a217444460d808c0800386065604f09001608f8d8126d53d92b0217061b0a5c89afbb127067b4b8f260cb39782acb45c08ec49e02020c03758289c72cb48c596023e0c46145e045e24f253b0a1712471258299b32d8313891d812b830f832ed809d890d8d1185111627810017045c5dc9ec2b495f2bdd56722e345e2c462c2e6c4604e9ed94bc599c491c28a7a02f4141428181e000460ff8023046c5c59652b5123422322175a231a580978d17972c145c58ec09642464c4604762c4644220cb01230a58aac25622761c762c63c237844f085e107c2427084a108c1f023812c0400585feb012302003a095918,0xc149028f051c0a2c1450287050c0a0a37c0c6818b0312061c0c281830303c6066800010326000419b4b4bd29ae8b74a4920bee9ffa552d34ab77f65f3bcae557362352c4ff52b1e21bc427882f1111c222844306c00c50008307059a000041e4b94a76dda44ca26aabac9a8a6a7f4f1dd0a52de5f6a94dc2849be57663c4e28adaf3e5eeba6f93f2e91302aa28d23c68e3d6da7e955f4a49a4fd3748a09abfe57bdb1d994f14198000c20b1429431864380cc231f2121c242848304c0373cd60c462cb49586ad84ec387ed88ca88c185c588ca961a2e042e44b2d71f64ab0159c9185118b0b832c448c5960ad62c2e4c460c7634f051b0e233258091811d990b,0x2042e04460c3214c204420c43643453b065b28bb51483098111890baf23812c249489649960a4604f5ec148c2924232342a04be04b2d4516171e490e2f22582bc145c488c59a02420c460cd0d3b0e150219125888f851d850f8122c5f013b0648899853c04bc09a327614b01270268098ec05d80700001177c5c2fa29a24d3d492295f3a37ac5317a9b8553daa549e374aac214a92fc298a94a72af6a8d4bf6a30ad4c4eb42b7afdbb3668deab600500a641147222e4445db0855d0a421474250849d08ba12130bc016947e68a76ea255df825e84bc096c12d425a04ae095a12b025304a5093c127424e0496092a123824684848bf053c0a6c14d0297052c0a4,0x2b4452089d1132225044688888ba09241247246048a090c12172401a004002154c3625f83c824caa8d024a1c7e17dea714d062f51d22aa5fe2146b351f1779f2b5465f9be97078b0ccfe3e2a48b0c4b00a24a0821e10000083b3f45162431c2700000256000018b23e920e0b34001022e3c10510e13f53f249229c63493229e2187c8486090a120c0f00000118d9604454bb452a4618a15d355bf0f57f209a8a14b952d55696a942a7e97854a8d2a5f97a6fb76c53b1bb6eb5a7a9d2fdb01a084696f97ec4e929f2a6e93868e243c484ab1c88b9111763a1304250849d0909856043c84c348c230258082bb025809781178100090c3c8c084c78003823643b45,0x5e91a4a0c2a797d44d12286dd0c551c696eabab4bd627569f98e92ab3a6e94637ea55b23856a960449fb5e94295fb952b72f0f1739ca8d6d5e5db085210a3a1304250849d0909836000000939587299ed0a32a25d12c95b52e47482085049ca162854c7e94a49a09d4be3fdaf52a5a1f297a57a93ad7a95a74ff297a58bdac58a55274de6d5e1f2c5644147824f045e0a0b8416082a104c1f00000119d002e5c7c414251cd054122a0b256a9a14575f0e9f8b17a5d797294bf24d042549449c9af175dab5ca529d215b1627cb942a5ca367f0b3787c3df025a04ac09301250243c497000010b7c00003de8611a5a94383b22b3f4649a26d03e9821a10fd11682,0x5a4918711952c045c188c094c288c288c888d085c296528e14b1158e8c688c0844788c496424644b11111e292e47023b065889d872c0560a2e3c7644d62c78096012a0251c49c09281230243c49f02c045c08005865e3a042204b0d001608b8083000d7e25224a3eaf4674001412b29865908b9f11832d648c88741966a2ea46a3ca9cb81118f1d892687298714970e911544bc185c985c088c28bc68bc08922c5162432c270011835600bc18b586800b05ac44585c1966ab35111e110a2f5e172259a910e002f063c011831e5e144258c308d081518f0ec92d4457dac9d832c74bc58ec48ec28e0a02f4140c283a9f00be06050c060f80001024649cb14556b,0xe0c2fdc468c5e4ca6a45e0c4604b4d5eead4560a46144644020c0035908b932c04bc0962276347604b01170617061702231623122312582b5812f7463c5e042e3446042e2476047604b151702471623123b1a2f0658691812cb4bc096122e04b0158c91851d8111811d83178b0b8117811d0498092c1228244e485c9170000b0cbc5c0960200ec12f17026b063b0259a97d92c15652b95170223ba592ad5574246642e14460c762c5e2446142e3cb09171e58ebc688c7960ab052f06171a172e231a233a58091811185119317811783178d118517870b831d8b124dd8222e4445dd085610a82128424e845d090985603b0247fe5d8a3832d256e2463cb512302,0xa4c149028f05180a2c1450287050c0a0a3780c6018a031206180c281830303c6066802b2159442e58d21a0124e85327a57bb5373a9bcb5b961bce35bf8bf28529e004a7866f898ff7ea4f962a52f7a15d05180a2414302850505ca1700004080c0008216e3daf0515b9b55eb30a2ca71c15537a5f9fea5e29a0c7f9a1c2e0121e24255d045808a411302250445c8a300256266104d164b228ac69caee10a38dc30535996ecd2a3cdf12b178d5aabad4b27a86322d8e23859c218aaa31adaa7ace2926a8530006024600001670ac852414fd2a54bd2d52bd5dfda45044daca957781152e833126030f9090a97602c04604b01170258080170cbc5c0800b8276e,0xc3254b21310a58eac74dc09e1290110464088a030b810d8709891374624201c5ac84d446a132ca30011865e460446044604008c237054754e0150e74088c0800b87368b2aae113b5e1a027889ee05bc0b3815f02ae053c0a3813f026e04bc093811f022e043c0b7000040cec95e8d000012307cb064195c5b4364050b207125075120836d2d0e9d05239a6f856ed7b1601495aad49d6852a5e94394a93eee18194cf05acab3a4ea5e352e55a769f8b43e5096f4bb612282448486090a1213a424306c0000017f15685351b9b295c6e73d555df825e84b8096c12d425804ae095a12a025304a5093c127424c0496092a123824684848bf05380a6c14c02970528,0x4a6045e045e14b0558eaf14d4193409702e252d2814e1d58ea7dd2a385396553a91658091eb2cb56122e1c461446242e046a64a9c8912c448c39022815111a11061d262c267088b91118913092c04983000382a62e0c4614005c16f14362902420801a052c5f2975246f45424e05053f64b2d248c0006125888510d11181002004cc010033e8f846ed4b9e1347c48a930300461d50047808c09602b011602230214026802210225901170218020028191918122a402002e09fac048c085008e0097dad0151e5e985c0850087408f0085c096d2a691b1217021e1e1702232a450279fa1224242bec0455d85c9902a767c460c46443e042e0c46142e04460c341,0x185d0844096a2a7d6b5c02760c8695b49c0b3103088d380400b8206839402a229380450b88c4965ab3d2c2e11022602470a233a57e691960a2e24762470d05032a0ee052c0a180cb001360580a805602280400443576809294021416230223062306375635aa004bc0895d81160116052c048c0960a2e2c20e42204b4d23023b0225021e02230223165c291811181178111810b8123811181119f38956da762ca00c222c460446042e0476dc008012f2612141a1702350a58291830b8b21248c39ac488c18444854792324614463cdb62291d17021002686b58130092f2928505064a0a011e0298b011702170258080230d0c7409439702586800b04bd60276,0x4cf6bcb73a9502601c4000027607d350aae952796b65872f37ae710ae211c41b8827102e203c41b0080808bdc137826704be095c1278247047e08dc1178227043e085c107827e058099810b810b81118123811981118100250e8ca40960276123765b891810e83118132813405a6a66442e14372ca1ec145c199cc8ed24abc098026a1446cc82d44604a62c460c462cca0446042204259232a310265a64cc8f872c345c79612b1eda45c18bc685c2893d80b434b6972e1cf094f1a3802150a682990e5214a4284832906120097011812c05c022e045e047c044c04b01140220021a023202320256024008b8112a5000836340091912972f2cb055bc900d2d445,0x65808a81178b2c14ec2868397843800143ef00220a9978316e4a8ab01580888908892f755111962a6a87b81113659a88812e54457953d2e44584409c0ab9ce8f0b8914fb0d1706110e586ac7e01110211061712171a1d0a50fc22b0d4028d050887120e000b04ec44197fac4aa7a1cbb494a092c14aaa81151e441888b0af2001415b72a96dbeaf7423800141eb5b8b82568a6b57d9090a60005091c4668a92a3ecfbbd374a198318616a4807045d84788a82a3f8056e2a3ee7a7d700b1802c01600a805402e1e80540280160e002895e4a4ca1a103681a434a25d02e81448d3f33daf14d2bf1fc6e8d2731ddb6e14a14acd2d64f4bd2e769d49d3fa1d6c5e1,0xd5b583c56fa3e9f8252a4b8f0b7bfeea920c08b871a9a7eb7f1d77f4fd6fd385a1e87a1e87fa538580167c05371780d076f0f2020b0025b7641521290561e3b39247244e485c9090826000042a78000044c3720515ae4b2c3d3952ade9122714d8abba5675fe3951a55a97aeedfbd4ddaa42972a54af4257955bb73948d0a55af46f59b47868f10de213c4178888209822612c700a381002c0fbcec18000029696d5aab5a119b45d48482a614a6644aac3c042e0446044a042e044604466c5e5ca68c5a14b35214225062f022342698919f1785119d118d1d8f178f118711850a87150536d8091811d81118111892c548c08640920a46048e04762c401cb053b,0x102170e39c8a39127222e44444130287460400683e750e80085c894b80220978b870014042c6818ac2599c5651146172217022a8a9f222ca7ec04002820e7ab60856524fcb81088508810d0b2c044428681844485c184409612a1ec54f52f0c94851291061a122d4b439a02400a00444085c28680868486808d7448e889d10ba222104c0220400083eb4009291025808002052c500800103b6b49170229221d0611562552042204e0d263617261d02704a1d50aa227c81512e8d0938050ca2214220c284422242224222cabce9508851575b6124bcb81297b011d0231e09bc127822f050441315d0a3a127422e848441300003045d012001012b02ea805202a1,0x7102c8c296b25e64004417f2b68011053d792229c5274ba91756171a2aa8b8b0b852bf22f4bbe8f2204222cb01110a170611065889511865182e04001440750f43d80ac94008827e004417317ea17021d6a58097554fa95e114a17ca1d4e1106110a1d0a588ac1496a722043a44b15110e230617025848b870b8b16d808b850b811ce511ca13941728282098143d0f4391021a021102170217020028201ac745cf9779628d050bff28f2e0ca3eea4820850584924a5c4850d89b9a061a0a1d1e2c22590a9f6aa55844b95bda89af0890012065c0ab5f934442901a28045804221cb0951ea42943d1f43a5a3c8812c154bb20e140a140a5808b812c350324b439,0x5d78012085800d052cae2d09170a1d6e55f5797021aa918d0d873cd445794fd5e5c087449e02e5ec35a1a37c9972c1444094f951657e5c586428742874184c588cc9a02224442381ad1df61aaaca566a22d4a7c8a90d810b832873be6f0fe1a3a343a04ba4c18913078200141af1ccaefbe52d2a8f2e14226cb3ec7449923506061da0a059846a231ea3000283b6007432351f7b91022f2e5a0ac1496cfb8578694f405e8280816050f43910211021702110250f43802220fa87220cb0d5a08897178543802e08391812f2474295f914e170e116a5ba952567914a1746002e089a97b9c8912c2553910211122f0251f6623a2c2244a1d5050181602a1c881001,0x6586889b2972214a1d1870e8308810883088308850b9b2c35539d0a53e4408443943d0e44188c185c288c08440961aa3e87e5e876c2450488e909d20ba424304820d80440904094380822178b81088114810885001105cca4485e596e216d1dce582ac24a5394b9182582888708933bf545411a295a118a58294832c357fb50a173e1706110a3516112e1d0a52e5cb94bd8288812c447409cb9d02342223c4278888e1114221844106c046042e04004442f114600160a5800b042c4f08af22ebc2a2c229cb295ffa92b01353a353254e00682062e043a346a44224cadf9ff1d55fc7c80899738fe3ca831f045608941127222e44980004885e0a4409c3ad2972,0x6b117a6acc5622b311712582ac34efb9f622ba4d29c3ba8ba77ddf105a20a3c117828261044170000f10cd15ff6dc00704cc003822ee1ec45602b0100060a595af2d14ebf0e003828eb15598ac85e2ab3977f6022664f0534fdfd52614bbe1ae5f87e5f87bbcbd84b87b054d260c4838b01002e08d800706bd35bfbbd1baac24ef9c89d65dbfb0ac546a29ae7931273e89300058be6002c16371f632f1dd95d3cd491628b1c2b0001845e3fd212c23e0300cc23a0e986cb98c918f9dbf77cd74db9e4f805f0300816611870001621da872e043a043a1400141731d021d0a00160e188a320a12cef08892c6445f96523a243a4cb6911161d021122170217021d0,0x6c58b366f82ac044c09c7d58b602f053a09301247244e485c909082e0780b87003c427780ac04013830e361c8bc380360ebac75efba091852c24ac18e8af8173fc7fcf349832ed82be35e726fec0555c7b0578293872d456022e44b01588ac9534d832d246c18d7cd8bc7f1fc3930658089812edd8afa12f025a84b0091a12122f814c0286052301d24005826e460cf0d7c28023079c4c38ad796027417bf612fdcdd56c2b151a2b9737538f602f7ec1569a75e6f8489852c04d7f0fe1af053f113c226c44d0899111e222c44446088df091a12302427482e9090c12087e0000e217ac0400383062e044e04e1cf813df35d178613b23d08bb33c244cd8003820,0x17870b8901ea3b0176060205984741d30ea894f80300244042404007844f580a3708288004047d6023204c05130a1a28fe112ed009410f193e170613022a88d2547a266c2064f11520ac3500a264ceb42a4a5464d230e60e7109402b0d06c35612c0d4db2970e4c09602b01700ac44b6025c02240cb096590145b01130278ab005c02aa4c087781410a4409350831d045808a39127222e444441703878bc39302780a2f80a28016215ac05c3f0fc3930a000e0bd89833bf7fd580bb7278cf7ed34eb2f1d59abca5e12abfbbbcbda560269f97b15588bc05362d82aef8e9d7b05580ac04d3d84a2f8cac0560a69e6931a458b162f1e4c3960af0513025808b8b2,0xb2e17025829da52f8723990b832c151c085c485c59dc885c19602460476045e04be2c761c5e14b01470231c89c111722222078000588a6d60476042e04002c213008e081806b042ddc585ed80538016b5123365f3e011e0078b8317c7239b2c45642765c8e0cbe24464c8e1c760c5e7c2e04a61cee048e04023c0032f0658aa3850b8b2c251c48bc29dc28847000b857e011c23f478e77022302474a5f3a47325322017e003a39d2f852c551c085c08bc494c188c89dc385cd85c591c08bc39ac28bc085c491c28bca91c097c09ac0960276045e34b055f062f02770623022f02260c477647f2357217361736171a2a230ca32861781238708970b870b890bc3,0xb8d3b950f8538fbe048e742e048e04be1cbe2c7c227044d088e11182227445c0003c5f73f023702003e0918bef1ec5f5aef9cce1c2e7c7e64be04be14f15172a77025f125f0a171647066f2e27025f127828b8b23813a78e34ee1c029c00f73f1c19d3c71a2712770a57024f1647065f064702770e222c002e2fd8b81001f07fc5de800382eef3d011e00ba7c5238d3b72edc2e4cbe4c2e0c8e1c8e145e3c2e048e1c8e24de2c8e148e1c2e042e3c035c0135f0a241c002e11b8047053ddc09e0a5e342ea4be1453e06070c0c18040f0005f112ddc0806b8006bebc029c1db5f8e47b25f2a005e0838ba50ba9008f013c8c09dc18047808e2ecc2e04b212f4e6,0x5284f15172e3752473616e047802e8e042e04729c2e2c020400f1f0e470a5f024706015a00197873a831e8100b9000c5c08bc19dc09dc291ca8e41854094c1984397c38bc2806b8006029c0033b0e341b30e8e047a22f2e01ae03d80d7036ddc191c085d2805f801eef048e042ea402fc023470a2f165f425f021706771647225f0e17065f024716171a47021706011e005af8b3b812385008f001ddc19dc091c297c197c28dc685c597c097c397c391c085c091c197c197c09dc1805f80068e04744147822f0505c20b041105c02e04005c4534706017e0cdaf871fbd0047040ddd591e88ff7808380262f046e442e644f4cf21170e011e029afa12f8917890,0x9f1b514fe7c8a954409215906415355f2a157824e8498092c1254247048d090915e0a30145828a050e0a1814146b018503060600680000891ea1c6d1f540050b3d5380160b98a85755d4acd4583c9aadfa1fbfb1e263d8aaaf2a7525bd4ed3d84a37a1edf2a152c0c86959050de1f971b202a5caf1e8330762595518b62435254963919152ffd78d0f43a8f47d0fc3d5485800142d30609cf5610595154f6b97fe3f0f262e7c2b4f76e8de1c708724623812f811b8100ad000c540994085c088c08d408a408ec0934098409a0202840035f0200462279d812f81118710bd0067045ddc191e9804b813e026800315abb8334244d2aacc468c8e6c2e8c8e44ee5c,0xe572ba0a2414472850505ca0a082e0000e3378e75a59a7dc003044c778288ae4d4000063c6ca4c371daf2bd1b4e10a4e8f6ed29d28d8629805900040fb894409a4be5a8f9094ed7d4ed524d8625800042bb04a8144001020e05126ee8a56916c311c56ca9f55b25fcef4fc1949414415ea537c9d4f52b7ef52d2e1a43048501c47222e4445d8e84c1093a121304220f8114005124c2821c100020f395d564a39c625578b8a5045418574e56bd6fc3858dce7bdedff1d5245fdcf4bd5ee78d2fe879b60a2b53f2f47c82a87afe872bc2c808285ab21a8a158f089e10bc2427084c1094211842107c01a0008346002c12f36f39a2284001c16b49ab8fcab3d5a3e,0x1c48005059d17c715155e14b7e9defab4fd0f4b95a5e970bcbd5e5e87f0150e5791020d9b20ae5e444dfc54916189629717550f43c52234a1d04e1524eaa5bd110a228b0c2b0000835e77df72fc6953aa88c328c2f0a9fbfd6f49830bfa00141170a88717a0a0e141828081e0000224d80000b8c34b5510a37134ec925a692491665f5bedf2a0d289ce93a163cbe0e93e54ab6415972ed7734aa589c6ed0a92a94b146e50a96014e82290451c8941117222220b80001826e6a000828e7a97838a7f6b127d442afa5bf5f6b4b28dcf76fe47555efd773fe68f8ab72cd2b95d049209239228242e484841700001087c3324a2e83c45fbee0924be4fa2534e155b5,0x3f9bbf57d5e14d65c7c4a7ba142d2e90b12821a5fd1e764249230b7a2a98743024040028366003428b11fa59489893404ff8aca8f2fd5b557f3f222e1c297e67d1e63d1fa2a90152fc3d5fc3d2f47d2f5bc80a87ab17dfe3e4151697e7f9f7d097012b4254049d093012122f014a028c052700003143c004869e779459a7409ffb7fc3ab2aa73490cea6baeb405dfd2f53b5ed797e53950e53e17ffa1f97a1eafa5f970a578d90150f57d6f212e1e2d82ba7e3f87e3f414f012a024c048b00ec4352001411f0a2a45429a7bed790d11065dba35f445e08b9117022b445608a9113a227044c888d111117c127024b0494091c1230242e4848400e80004822698d,0xa3ebfa1e871b538dbb6229a77879090d9b5bcdb05110e45e1e8f0bd3d0f158f089e12138426084a108c2108360001215fac71ad155715a088930db520a14d50e440920ad2139f66a49cdf34116f6ff3fc79ce552d4fe39da1fafabfaf1b4fd7f612a1e42547d3eb7872634e3f87e3ec14f822e045608941117222220b81d7800a093973521ab05156a1c0956415d4520298913885d5ffe0f53f2f24ae1d5153687a1cad59056de5e8791173f87f0f632e3e42520a780950126024a048c092603f68007059deffbf8393496a45bfee2c23ac8292556f6fd9edba7f20a74151f232e1c2cd92152f21ae7d2458a2c8862433c2703a269f3ffffbf42382793b68afb,0x95a08a8d28595272a1e44417ff34d48abcf3756868e155bf1fcbf5f67c50a5469df9d2b22a935480a425148832878ad7e829e049a09241228242e4848417017456b8a2a4345f9ffc3d52ab0aa7e404d797f23a91155e1fa76c21504290851d093a121304220d8000385de00001670757f7e2bb6a2f1413228d14979c285b52aaedd3fe3e45417d7c1e44455af0b4feda3eef3ea18c321c2b687e4ff274d16eef910a71f23a69e425e0a0a84b0f12a1e295f43a14c2d68695364748470576855f800983ae5a95feaaa2dceb2140303878a4408000892e001c1cb000a093a7746e2e3eff9292b88aa739f71fcf3414d0a2baf1ee7901488bc7a1eef4f47f2f47cd,0xdf1c54577e4e77c7f13c8ca435562f8bf424942c82bac88b9f5ad524586258a7d54428a3ae3a4e3687413800643472f0950547d0f4f8c6a2950b21245161856062434b753e060101c000044b3000a0ad8003061cfb2e1c8830de47408eb2e1f8729eeea0a879150f0a4042bae3fbfa1c2c5575150e35f47fbf169fb3c98328790150f53d5fc3f2f5bc8282cd9090d90571f43f0fe02d053c08b411482250445c888882e0000a0dd8504bda001c1673e6a8f2a3450528aefef714148eb405e39af27a2ff87a1de7261c0b47d0e4c69c7f6fc3c84ab7a1e4354be80b87e1c6c8082c80a425178fba3787b093c0a3414482850505ca0a082e0000e097a514fda79,0x928775212abeaf93d50e282a1e8f38550fc795061a69545778a29d79bdfd0e541953c8a8af0bfbf0f4b8de1c6c82a8f561452a67b7f21290d70fd3f1f4b8db053c04b009501260247801400912ccbb2001c3af15e00283fe6fe97f4d5bf73f5e67c8ca8f0b14e7b5e9f2204a1e415962c86a2857d117222d045808ad115822a444e889c1132223444445d0498092c1250247048c090b92121003a005001c9432cca8ffed2a29bfe7c524efd9e13452d69ca8121e86aaf8bd477b0f17c3d2cd74116022b044e088b9111105c0a1c007128c00383b60e100020f1958369584d455458a449254df8792965efd5045fdaf47c82a84516004931e2b5a1e8fa5e2a11c,0xb52001410715000c1471502151a000608b868b0b9732841b77dae00082562dc5756f9a28b7b5ff72284a5fbfe1d502c18143c500144ef45b0159e8007062cbaaa7cd6457801608f85643ca3450e49cf22242bf9f7792a6ab75653cf212544619460524be23452c4956431a37d734764a415302c605070387a1c009138c16404001835eabc88129738d1deac446aa3452bea971ad2b09764e9aaffa7bad7d5e9fef2b73cdbfdf79211a69511986c718c58080051f5ca8a159001208195652aab5c005045c6f96ee921dd48abdf3a6fbe84b8096a12c025684a8093a126024284848bc05300a50146029b81202a1e40516c0543c80a87a1f4040028bfe002c1874,0x902f204e405c80790660254b802c01600a805402a01500a0050028011002001a29b937000017700040998cf0cd14a81a40ba05924eb39249bf37928eab862a59b16a96f6e2f0b77e6999f742d58bf27521da356bdc2338457088e10dc2138417081010f8ee099c12b8247046e089c10b8208047c0b01170258088812c045c091c093409340904090409040904090408c80801489f6b7d00160c7ad050738773801302be530c5911702714acf80156fc6a8111126256a1c52342204b0d110a50e9f9d0258292d5f02ae09110650fc12221ca3ce870b81380474287408a40874087418740874185c285c08f702ce055c0a38137024e045c084013e00002289a404,0x854b900f2020ec0404e807d00ba00f40412c7806f00be013c01f802f003e000680952a50e54a1ca10852a54a96284218b17005802a01500a805802c01500a80540224042004200400345d725ca002055e15516ca992681651161232551209ff351026893415b733f2ad4ab78a692bff0c6c4ecc2ad0d0f958e203c4042b3c8239017201e4041dae813d023a027403e805d007a0760254a94294214a14a10842943802c01500a805402c01600a805402a011002100200122b7800005cc90ad00080c98002040c7b9537563ebfa53dc2ad4aae3425faee145250d478df6a37adfe62a5f34ea4b79b972989eb72dc214b15ce211c4138810101e20215ce413c823,0x254a94294295287284316287c0497078b802c01500a805402c01600a805402a011202120210021002000e33192852001047e27500040c59183292851493514d355a978f0a6ff3ebb852452de969afe5820aad11476376971a8d5ed4788])]),([0x1010101001950e61e2680808080150ca61e2680808040150c661e2680808020150c261e26202020200c84261e26b],[(0,(0:Int),71,[0x54024c022620101a461042182c02426064244230486060284158484c282a284c60e784a30513845226332504b529a83c432292d19c91e6846304c3452384c3006101a22121405182c2c2114a221a82222280c2822341121282423228824921a083405321824242238111c180e2a28380c22090c063844304930d81413180b3412341428ca2405282618062411308c2612088a2823111928a8301330091805280622302425221130052809301c3258109c242221312825240320b8090c3015109420b00a092228121130982134300e28281118180d1406212c30121218282920b4109a20aa120a2406109828050a0a213820b218030c031209088c111401a602,0x62a0c560e1890550caf0a8346458e49f237917cc2d49623b187696b4ad22658b0c18611a905e1a0c98893ad2e6373a311890991098088c41064110888a4119009880960094808c80929091480a80898413248c86064212821e02084606821442188210520e4215048a8a1c028b09129204059886048494451e22100e08451252080c9290104c1c0201011611128882029615007992a04620a82084208620054b110680c688430e686b8ac182a1c2304b968a80bc85c50ea26d386830383034156e1a80ac44e2e15087939a9ad516a6754d6a3e41f29710b6c4545734660e161a321c3088b953ae2a8482850864a6045404640202c200a7014610458044150622,0x111a0211940e02120b16021482111497030c42109098051c0488848a491405105110098c0612231011901a8a05080508809ca416611018900c94261014901a125811108849104e180c840490071005900d100b100690d01402024203011a191b181a1095109490824114501310080594901250121a00b90804094820202d6c2c36183518340c2c8c288c0c0b00e207590700a08058847413b43990a4b0909844a220090c8625048281c281a2816161013102806321070106410521041146210253050946888302a508a48863052284a416270c4689821321c2c1a2c141c2216520c24d526312d1b6e4c218d704a1c320b63c218c989625107517a9a32448612b,0x4685a5e8f90545e3e405c7a2130c2318de72fdf79b342f3f566850a384184a001030e0a1084665142942850a32a0e5d854af53108d8bb46b4294ea40c0600634048c088c0858085c088c0868085c088c085c08680983a30200040b19d811001118102c009181118122e5b0160e8c084a096022e044604c1cd0111812c0595181177b01170270f00224443404b01210223022f022302580ac045c09602462c76044c045e04b014008a81128111813804d6c048c0943e2e80096024004460c460438044604cb6022804b0517021702100228025e4038f9483c806910c14a61806080989876222165844a290901088a888948a90d2100d842164210460c82028215,0x4a8102850a00083060b4385909580ac0562a2204a5e870a16871ba020a3328b43859a7643543d1f2daa1dff33ead2e342d6e53d0f4bd1f57d0f778790129f00be00fc02c0a1e2e8082c5a1f40400182e6a1f87a1ec05142850bffd0e19a15e65439c28e74dbdbf4bd5a1e424c7304e603cc0b02285a1f878b43c8082850a16c04142850b6020b602f01000a0a182f80a87a1c881287a1f40543850b6020ba025a525a1ea9d08bc48630142d0f4380020b3ac04152858b1628c8b404166f0e003831e4c18000c17f1cc82800e0cb9909a88d42659462404004831e1c0430c070262870a33a0a168736d50e16284cfa1ce7a3e879a16b71b43850b4385a1e2d0f1,0x4285080080e3a9f2bc68d901586bb70d553faba69eb70ae82577be3fe7d4e16ab5e16974218a1c2d0f43f0f4380020d7b870a16c05142c50a142853dd18e146fbc8d773da76a7398f4fddf93d2e562b9c42b8847106e209c40b880f106c0a1e28500042d7155490ae8003042c86020228404046f708de119c22f8457089e111c21f8437085e109c20f8417081e100347702de059c0af8157029e051c09f8137025e049c08f8117021e05b80162858b43c50a10850b43e8082c008000063d1488109832872ba1aeb61a8be2a2fc5e4142f1e142c0082910250fa12c1f5715550f439d3514d0a56c7a3c28de1eaf2de970a190131cc079818763a817501ea0b801,0x402040405c80790107602027403e805d007a020963c037805f009e00fc017801f0017400c5a1e2850a5c1d2800012392a4e9b25617aa38420ba53d5c59b74a729c315aad4a742b35ad6314a76a16974a14852fcaed6381380260048008801260054a14a00104764a12590be92f251024828d4a353d6a54a5bb38820947baee315a85a1c6950a08b0218e03c71060203c4042b3c8239020202e403c8083b5d027a047404e807d00ba00f4000a050e174054385d0145e1c2c58b438002107a285e3e878b34685a5dff7a90b8a877491d90d4b51eed2e14b7ab14c7a1e873b190d486a2b9c8239027202e4040413002e808285b01680ac05142854b43f80a28431,0xe04d0461907dc037806700be015c0278047007e00dc0178027003e005c007806e04493457a4c7b6352d59b7e951a6f94cfcafa02f005c80b8016a02d005880ad015802a4052809d0138026404a808d010117c027004d0098012c0250049008e0118022804300817400a50a50a5ca942002053e6a0ba2bd1be94124492095f34af0a351e6a4a72de8f35e2b7bf29df005c00b40158028004e008401360254a14a152858a1080001379214d547f82a85d56c22fa2dd1e65e5263a34ab52f0a50b15a8d0b9500e0210008267050851f103686db2ad738d596f5277b14a9cab5045860580800022d9d8308a8b89698ef010c0214042008301040204040788085701,0x10a14200c85b6a7e879a1669d096f6f951ed6d4a14614a7c50b2bad80526876bd1ad6dd263c0697fe3c3951018202040116050f43858a140010b1c10b58cd29c001074d63928a4f4539cef62d5fc3c58a1697c3e97442618462870b438590150f43c500142a365cb83850b962858b15f700141274518d54f9aaef8d1b57d0f16a98f546d5f1601414a7a9e414552162c51c180808a101011a780014b9728500042f7000609789d4f5292ad5476a91ab51bd8a8f9db9486290ab1a352f5400008159821400104bc8d9865db49ca9d7a9e71b8d0a536c257296712dd2b72145162431c270000025e6b0c5c4cc254594d6ed549ae759850852b15a850b4e1808618,0xa5002431b055f35c00204cc4ca4fcd70f2eafa4df095db04a8a90e62d602416685cbf52154142028282058014a1000034327e000820e9bde83091a7ef42d5574e5aa5f14a74b12a9fa4ed52b57af66a10810c53012004e012500382f70b08ba410820b20ca967785274b94a4e93ace342a8ef4ae62a58a90cc041008101010aa02020eae050e18a])]),([0x1],[(0,(0:Int),10,[0xa108431421084210a17c05a02d010522042204901400a870b20220048a440943d80ac05602c1f40431a2bc3c849411906c42658460c8124044619c3f0e17974018a1c2850a30208476092222864c464c24052212820e5829109202732610888843919cc7d456a275cf684b4223c34192a1c2914661465132516220d190d188c988b150b148a948a0e127951ca2e50f26b931c97e437217961a99d41eb8319f8c8c4562c2d29691b63c249148282c60f343588e08908890485042844c150c144c130c128d110e10880d080c880c4488848848064446042602848244418281824142460186014500c80b080a8807080685018c5842fa81d6172071d148c1605282,0x162842147a4142850b16870a142850a1787901050a14285e1e4052020a142850a8c395ee01bc033805f00ae013c023803f006e00bc013801f002e003c03700e8102c5a1c2853b9c0a142858b43850a142850b202e1c2850a142d0f202901050a142cde1e4241cae710ae211c41b8827102e203c41b03405a02e1f40464084409c3e50])]),([0x1],[(0,(20:Int),2,[0x1942108700583e00b078b802b0160f83858a1c1ec049787cb942e5cb402c1f2e5cb952a5801500a87cb9728508644502220e1ce8e6c7303951ca0e4c7247921c88e40f343591ac7d5c6ac351fa81d406b2314988fc4562271018e0b63da86d2568cb435a16d09682b47d3121850c18423a0dd1a82])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r9_ok : checkRowFull 6 [7,15,23,39] [31,63,47,55] [10,10,10,8,8,8] 2 33 [(0,1),(1,2),(3,4),(4,5)] (forbUpTo 22) (RowSpec.lemma36 13 (-23:Int) 23 33) [([0x68a820411c950804238aa108046c5310208d4a640211a54c84022e21881045a4320108b28642011e08410d41f31a81083a53512007466a4200e59500841dd],[(2,(13:Int),2,[0x60f83e0f83e0f83e0f83e0f002cb972c50dbb35ead3a33e6cb931e2c383742])]),([0x7643521009c8ca204118994804230b290804546410208a4c840211459084022631881044a632010892c6420116190c8402183229080428635210080cac0420e15584801df],[(0,(0:Int),2,[0x294286285ca972e50a54a942872e5ca952a54a10e00b005802c01600b005802c01600b805c02e01500a870dc687191c587131a772ee3db3b5769ecdd97b1f53e97d9b2e65acb395b2ae4ea9b52ebdb766bd5a7467cd97263c587061782])]),([0x60810a68ec8e510208d1d91c920409a3b2391408034764750810a86ec8e40c2090dd91c81440a1bb2390248043764740810eca8681922765021291853b181094a485d94480a4a24ec8042525117641202908ec2041109d880423142eca4205230976312029248bb2108148a25d8c840a40bb10804416],[(0,(0:Int),98,[0x8ca858d0a6523044c1128c063838e0d112c58801280e80a806802bf76dd9b4c4cac34a0a5439b047b422155ca838988d8266095832ee8c18f4aef0a8c2630b1c266461a640d516bc621f99ea1d5954732b65ac8b1a5c17e8fd9883420a063098c253868ca9288cb192894a943260e25322444d1238bca1c2dd1da7f6564b3b4f66ea79a0e05eaa4180a658940a509942c45da150cab0195a468e2331b0e3428344c8300ca0b1c68a98216060624244bba524a4119007193342448c0c1c44e18d40b90f34284f9c482725960d182ce0b38a8e2c280c48938a4aa91f461a21f5b2e4729a1683d12849db2a32206050b0e87b0b8702965248c9c0c06e032264a282,0x1a8de8515cbe5f432a01150b41aa1d9c9304872458010842952d3ea18d0a73d00a5755ca729c93583c0c9da4a6189c0420e209565db9fc4295e196ad2fa7c214a5c3d2a3b00c00a50c42d387d861e0e161852c7f9c1d300acb77285a01058b10d028a7c3d2b3925c90e48b0020414214820a8043432f877614304247108581961f0c6e2ece517283942c00d925084d7861bbce873f0c35b8bb3985cc0e60b012f0f0024b202801250a508b08214a94213271c5f4a8d9898e330342526ca4c715a2d9298e2718c120212465848350986a302821551c6a68d506c84c71184a044a848a94283bce4c233054e62304ce5a1c248b3e5275494b4632143a74c9c2834c,0x408540864085408540854086e5816f776d14f16c3414ec50b57d0f20a0a5b950a4438169f0b43d88a8729e876720b901c81600d0b438d14d684828d33f404678dbb57b7fa122234901052a2c8a54194385a1c881242560270254126090e48f0249428a6fca813455c7d8e73911654ee3e90bc5543b81460a0e50b022c50a3220a16a7555051a1488705845b8a2a4a520af05293652638ac0d68a9cffba8b64a6389c16e8f80302873954515d5597ccf1a682901690a972a0c9095828a892ee809e0950498243923c09014009244aba3b00ac051bf622d2d52e77e2f632e05788ac1484e06442ba0a94dfabe9fe1eed2ea9ab1d17f20a9a9874301d830e8f40f0,0x2f253af6f95e842814298fa0ad01250225027848a8728fa1ca810a873c1494185408b048300a8f0ad3e54294bd2f14a8119d10e89120580baad7139f2528adfd828295f7429afe7d3f20a6dd48b4431c8e3df4a2c22c90c10c120a6271282bbcdf2dea74c314fa02c05202b0150fc385000417f0aa8a854a368f469408940916034441857c24440899012502110623e0c080e01be457964a47a0aba35360a1a55281128108850a850254a8d12851003721450cebc5444989f94eee8f0a92bd28b08b2430430482989c69c873444186b843e0222241bc7c62ed30c50ed384ad56bc3368f0b4edbd0e8c60ff33c28e2928c0dc82800a0cf8720d86430640854085,0x6d22d10d32383dc299e146445be5294584592182182414c4e01351220cda8f803008810881287a1d39416872813ee53e46c00a4645408e7d82aa74a044a0428142a342a042a140b4391022502680a2bc12a093048b0068474a8d2bf2a0cd0d13020d0b60268453a21d12240f00fe52e23febf0a6785a7ca953fddf622e10d16d22d10d3238a7c144eea4a2c22c90c10c120a62707b8533c144682a1ec54d7a618000413b343061d1c0d3d69e850410b6124a044a04a5ca853254092120950625066809c093048701cf6fe870a6822ba02f0d52e17445a0a4a2c22c90c10c120a6270ef99e14c7e9ec1553d1e342c58b36c15168747c18101c00b16873d51aea9,0x9d00e810205807008142e0082d0ebf2762c29015ef14a7d112787ebc9090a85a1f87d0524e9408940844285408f68f2a04222c4a0ca1dc0906048482547857d808a83088102e50950e150234221d12240b02af4b55ef0baf60a622e10d1])]),([0x204081150ca1d9ab020404a8630ecd581020154308766a840c3b1081484061d8480a4b],[(1,(0:Int),28,[0x2021ace417203902c090105d0114fcf85e1c29f0e68086f0f36871b43bb82bc14e09f04b823c10e09b03c04540844096028a14285f0150e162d8082c8082d0fac20be022a0431ca7abe6a116086381c50e5f852bcee542341b0c8606b52120a11dc48205098f164063444405100ca501244a033888c1a1420a1a3220c4808186032ca8b29286470d282c47a37436e841118135a3a9551a8d5d2c22688590ce87d732c654c9591b21d4388ad922380ce053870e1238d0a902840b103024c0521681cc0a45d2052428a14080c9092460c2c2814921228493b8761cc4a061432a1132184942448c81aaa4cb10a24c0321508981230e06216044c1224e0a11285182,0x11424008400842c91421085311490580127a8421c3c23707c1f28570248121c445c21a2da45a219299458459218218241ac4e02adc91e040c20410103c00843253482322f0e18b00220448b10ace098048021c11e00429db772b5ed3fda71428621528458218e07010b105287197ecc21a1e286284295343a4188bc34e410203902159d01e80740d801628daac041508d168d2fc6d1e84091e9c295c1ddc14e097043823c00d0e10a142c50842f0f83c80ac0410a8b1787ca173f2804bbe2d3e146a116086381c0558505a1e404162737e1d0f]),(2,(-23:Int),24,[0x80b070a0028a6a870a142d808af6bec04762c62d0f17c15a02a3d001421415494285961430f978aa459459219627014cf90177e7521c333a89624043822c10c70384a952a54a952a54b0024abf9d0206094946e80829406170245e01168810744c94a252285a848c062250819122481c2468e943148b1229489123224e060a0cc12342020531b0d293890c2324848a1217084c201430a38d0e3230a4c1c1a045012a04901120430134047010a04e013204b0121688581018a1410148032464c090a249183068a1130a8c4838140d88630089183028a12201900c1030c0c44c191042910a8503181822612126028894444940623db80bc04e01f00b803c00e01e,0x4ac8084c0810ae2d903a3a34a03387e3ca8512f5c056048248299520106011027748a9416352a0c8b91aa0d9098e23048806028f57d0fc3d0e14320d9098e2304008160041480102142850d0f43858a0da220c29daf00a0644409a0a0a12bd278092002850b43d0082d0082ca482e80828421469d2df87084ea7c05202c1c3c7f])]),([0x1],[(0,(0:Int),24,[0x97db4a942d0e16b612a5e870bb72b3905c80e40b002c00a8051707085285c1f07bdd2a5921052759e87c3da74a1180a152fdeac104886014410a188300c580ac04ffd80a87b0150f602b0150f602d01580a8746142a0434042e042e043c043a048204b012302230223023b0a260212022f0260ebc0960252045e04bd01840284083421604401902258091204811c0220300d68e85509a20645048a24ea5d872c649ca2406121449210403102042a02042808814204940a61083f4388dd072236028884205040c2024a241850e121244488280c842220417a806246140c10284064911428609040c2029088031894303044c1128c091224898216091830283e82,0x70e1687e1dd745421801536700a2acdeb5c7c2152a5020810229010f00285534b43ad9b3bbd4ea54a5ea116182c02482139f32daade356d0e800510680512491beb42ada1d29daa0d9098e23015a89bf108d6a1b7017809c03e017007801c036072042a7a01d020eaf00f803c07c025504210a5e53a36ab46954a54bc3cdc5e874d0f159c80e408567407a01d02e006035])]),([0x1],[(0,(0:Int),2,[0x14a94214210850a942942854a142f00b2e5c0125c1d2e5cb43c580150f83e00a4041b090a2428889223084a213060898216081418508113024809112080620ea3d43a674ae91d17a2743ec194b22642c85502a044108011282]),(2,(23:Int),2,[0x942162850854a152c54a942a50a942a54b942850d444490914248c10b040c142840a14244091818406081860508144048812224080c40284081018c8403db80bc04e01f00b803c00e01e])]),([0x1],[(0,(33:Int),6,[0x4d277017809c03e017007801c036065ca9438020a9700414b8020b9528528508680497079014508500c06a2430ed1d8bb0f60ea5d47a874ae93d23b0e58ca994b2664ac8790b20e64a8950aa244608a10b82])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r10_ok : checkRowFull 7 [7,15,23,104] [111,127,31] [3,3,3,3,3,3,3] 1 13 [(0,1),(1,2),(5,6)] (forbUpTo 23) (RowSpec.row10 (-9:Int) (-4:Int) 4 13 17) [([0x366a021653286cd2240ca650d5a484194ca1c34821b293b2328810471329008470b2908046a320810469321008468b21080466318810465319008464b1908045a2a08104592a1008458aa1080456298810455299008454a9908044e21881044d21900844ca19080463ab19080413b29908042c321908041c2a190804231b01083a29b09003a19b10803931a81083929a89003919a908038b1a010838a9a09003899a1080387218108386a18900385a19080385a],[(2,(-9:Int),6,[0x142850bc3f0fc3bfc82108500108421e1c284394e1d064e82a7412da71c3f0e142850a17870bc3f0fc3f0e142f0fc3850bc385e1c2f0e17870a142f0fc385e1f87e1f870bc3f0fc3f0fc3850a14285e1f870bc3f0fc3842108ef1a4e45c14a13a12a0fa09a03af1b0f1a8d0b8b47c787ce05ce599d515a7c3b4653463344d34563435133a3e08506d0550252b3e689603d00d6866768da0e97ae1f17683616e9a0e25cd19811a0bad1640ea08a02a05afd99b4e3c1b4363455341e34531c9f03281a969f37005565c7cd0f0d138d1683a82])]),([0xa2c5d00d94a51933909b294a91a741563293234e82ca652a265d0158ca5146b902b194b860437652764c046eca4ec5804dd949d87001bb293ac4845763274c904aec64e952055d8c9ce14233a993962826753272a502cea64e52a019d4c9d82433a990302857632048506eca400ee8642016a0e8a6c1160e8c6a1188ec2041184ec4021182ec4201148ea2041144ea4021142ea4201128e82041124e84021122e84201118e62041114e64021112e64201130e86420100c6e0420e0a6e2400e066e4200e8c39c8558ca4946b9032994a4c805763274316e20ac652462dc4194ca470d3a181094876],[(0,(0:Int),45,[0x3146000505cc9831602b01580a87b01580ac05602b01580a87a1e87b01580ac05602b01580ac05602002c11b0ed10cc0cc64c4179d15486e015a0aa16a13a0ba14aa924dcc8d2c80da0ea1ba0fa0ca09a546412a10a11af1ac4a644d168c8b0346d917a1aa19ae118f2941ca18af1b8659335c4ddcfab15c83d0257601abd189e4b642281680ab37e9cd80e81a802b82612d74d412c4f5298514a5816454f0da52a2345453ca64a6d268a330a2a88d9dd1e194b96555d4a4993272bb2236a372d148587315861cd5c868b54d9d11991879531a944651a597094555b155957098a328a51699639e1568c46b9359c35c958d58b9475a9281d93993399959317682,0x9fadebfa9e87a5e97a1e87a3e2d3e82f143d0eb5a39d55f67d4e53bbe40bc807902c0a1c28d28285a1ebf3b47d6f4385a1e972fca85a3c2cd9a362c5a1e87a1e978b43d0f14285de2da058b8b16005a1c2ad2a878b162c52a7f9af36e8d2be87a1e87a3e87a1e87a1e87a1d2bbc6b40d171a2c0a1d6d54fdef4385a3e87a7cad0f43d2e3687a1ea7a1e87a1e870b4bd0e95d0681cd07002d0f438d4a87a1c295e168737ea7abe87a3e8f29c6d0f47d3e95d1443e883d11602daa87a1e87bbebfb5d2b5abd2a54a95de39a070b8e16050e37a4b43a5b5e87a1d2fabd2a54b57d0f43d6e83b143d7e9537a3d2a55a94716ba1ac0a8906e28716d20bc36e69a4a92,0xa1e875fd5bf43def7bd4f4392092a5702917520ea458143a54f557f47daef6a7addaa5afd2fabd2f4538a1ec0543d0f602001419352ea7d0f43d1f43d0f43a54a97c01f801f00b002b5f438514d51f43d3e6397e14a769cec50ae8162e2c3801429ec82bee5bd5f74685ade973b142853a16970a5505e287a1c2d0f43dd686447bdd8b16285a1e28d8b43c58a162bbd40ba807502c054134e57d1f43d0f47d0f43d4f43d1f47d5f57d7f4bba058b8b0e02d8a87a1cafa3effa3e])]),([0x2224181aa10438b562248723652942150e2ac65282261c158ca4305439810948609873120290a130e642052890a1d8084a50914389b294a1418762102922150e2ca65242261c194ca4906439329948a128740212914230e824052810ea6c11410ec6a11a0c21d0d94a5050c381b294a2418761202924430ea2405224461d0840a4121c408220a1c80422061c8402340c43a2b194a20c8725632922430ea42052488a1d4084a4221d94c22c0c43a3299483e],[(0,(0:Int),260,[0x6090b002990b25181219141c162a119815668cc2c0e2130182a3b7e9240202c8a40dd4858188cc04868a12488c488602234b02c359992860b07192038c2408c409840f078c8404a40f0984640701888c89d50f9a0c0c069ba84528433356bd059132481eab080a8809881152912285284e084d105801f2c72fa3362d9868c5d11a94c0785e536d603052688ca92292041af88a2a52428d194436044602c5225c86ca238223278da26ac3ccaca3cd2c92c9bc96f1ac84c41d965984d8d90793194511d62b5324728729b2573c2b42342a1a1654450b42e7c6e12571560b49e7035265244ce50c4e670560c55551572562561546e6655a664470d545645428702,0x8b3e6d3e2518233e51109411180c03288335d21c03188324833698188524853451129f2c0522b03861060561112368c829481c32182618971e1f1c9f3c313c43190912093e69188a148a0c8a351e34290d0601a981f14943e6a228c0ee529c35b121262234249f284c288538051c051c1f189820b1016a22619020903c543c1a00eb49a012a88a2a0a149f3ceb342c229f3ced3cea34323d6e373231063d6b119a2132345028c535d11299222620a67e68460e1924c40d191218088c254620b4180b28c928e7c513c52080d160a231f3cc40c062506180e38062c060069165a1f28661343c6a284a0e1a211803c488b140e06440aa2e6510289f1c571100a668,0x1c289c199f189f0e113cec2c131c13291c1d143e7a2c9424864665091207375012d74d51a09248f3d69260902682282ea20a1c0d3449386d371a3554304635191c0e26323531190a34251a0a0a0a02a832a325171f248c29060d03259f1485188d0c053c9a2406150634452a061892250b22b81917209a28921492066588c1a170286914209c111416140a0d3e4524940369a0c161f128c148326051666646288d34310c85110c191828c415183e793cc2149132611a3131352254e4e54d552b5e113c323c253c23288934b2110921093498251f20e7852230a148c250321a52a0d1806280e01ea6061a06142510983d0b12123d443d54090e090c3d1e264511,0x93d4e2d4e1c263205271f351a31971297228d148d118a24c53843261a1c0a355135432338352b219a171a350b340b250f290a248a2323241425433e353e313430271628940b0e111a190c20a53c8c269f169f288c2c0c2b0c150303a8e06119f345428c3371e19061a2c2805373025112491211138123d412a123212261224922512291e161215122a343e6e2c143114251420941e555143e1d0a0e2803361a35982a0c230c11c741d35d00c831197290338032c0336b1340c249514950d0c294a1a05161a210b128716052c543c4408c7250315035411c342831315432542498209808d5605487d793167ccc3c9d3211221132621c3107e47446c45c744419,0x48630ab2ade974a18b85205c2bead4480f0a612c5cc96b481b05609c2f022fce2f022f022fae2f4e5a69704306923e043e048afb9ae9ef7c579f57c5575b7aa7bcbc2d19113581721191d19344229192a992c9f191f299922192a19291f2a1a19d6d1f2c9a289a221a34411a9f36413e322c9c189c150c211c1b1c2a9c250c2b1c2ab52c151c1514152a9d1a9d2c952405240314033c6c3cb21a11191114669113cd42d111d112e112e122c921e121c92293429b32d1324131d13218b21100c942606d143c5c3c391a3222657e7cac11993464345a34c52e192199129131873206344a35d937180d091c0b386434c334ac34a3340e348b28091187188929092a,0xfa3e9fa3e97abe87b0155f61ab0559f4bd92a872e0ca1e87b0150f4797023bd0b4211f422e843d083a12e02fca87a1d62476596025652a2a87bfe87b5d1d02580acfa3edfa1e8fb3eafb0127f6fd82aefa1c885287b0550f61aadddf05a208fc117821f041e0970287bfd000a0c78ec52ef56023a04a1eb7a1e87b1d58293fb155b2ac0560aa7e00543a4f602778c68182e301c60f0287a1cb812c054380160c3a87a1ec057e258574c96c543dfe51abdec055fd7f64ab0159f47d3e97d2f602a1c88d2c1501ab0158690660005085caca00141a758f53dbcb81500ab0151f43a41c25b9d5a547d0f6423a0c44385615aeaba5b5592ab742385912f6abfbfee5,0xb7a168422e843d083a1213e4260f80952d0f602002019750ebfa59158096149687a1d58543aaa96fa9d6357bd8c92f4a4aa2e3ca1ea7a1e97a1c8872872804a1cb8329fa5cb8120048870b1a001414757f6daa9ea74198002c107582ac44d6cc5612abec0547d4f61ab111d12582a97b2d110258096b52204741807301c0b0150f43d80a87001418758088812975e9110258895f4b22a7d56547d1ea8aa1ee7b0558495d561ab2953f602a7e8fa1ec254bd88a87a9e87b01582a97220cb0950f47d5f47d0e5c1947d0f4bd0f602b01110e170a50f602a1e873a042e0474110f220e44580ad2a1d5054bd0ea8a5491d021d0a57f602b0958e7409612adc88128,0xc2b4051f0a2e143c283852e053e74b9602bfedc47428b025fce8316f4f848de91a122ba450483e905d207a407488c0a1c8812c0543d0f602a1c005076d43aec888917f54bd2eabaa9d514b7d4e4baafe9fbded7563aa5ea7b0d582a9fabec0444194b970255f43d808e8311262b754d58095454bdcf4faa68e81287abd50474395fd0f47b5a1ec5547d80aafb25582ac5444394bd1f662b09170e3a2807d007a02c0a1c005069d5b800a0bfac04b1aa3e8f55550f539df250f5bd9c8e8712fa5e972e04555170e54f602a9eafb0550e440961aa3d6a5a1c8812877c0c6f18d030606038c2601d02586aa7b05580ac95479d163da9ef7bdd58547c02a0054bbe1,0xbc1b4031f062e0c3c1930000b076d4bdfcae94afa58d50f73d4f77d6f7bd4e740874b964aa1e873a0ca1e87a3e9fa1cb9b2b7b1c8852c1543ddf4bd7f43d3e95d08484f9097211e421c9809687a1c005072d43a54b4f97696b4aea4dd6926a03547d9e92a4f73926a2349fd4f4bd2f47d9e5058b687b0125e94b832cf4ddea5769168221c04b43d0e0028396a3cbd543d8e4c2a1e87a1d6ac2a8f001411b120a9754159f43d0f5bd9e5cb943d2e7479672a1ca0128f4b4b970a2d7ab508e0005072d43aaeba258d2500141ab2a297355fab89aad2e04a7d2f340c443800142cf580ae3543801613388a728fb1950f5fd84a9fb1d584ac4553d82aa7b051a023b,0x7241e480c98143d808881287a1c00507ad43d0ebe2a1e97b155baa872e0cb012cc8b8d0b852d056125515feab2b9d51474194fd4f5bd2f47d8cac0567ddf61ab01580ac35612a3e8f2e0ca3dd030180b52add5c547abeaf7a9d504b723a0cb3eca5612a3ecf547d888e892c2557d80a8f4b43d84a87a9e8f75986830300c58143d80a87a1c00507acbe2a1ee5543d0eb0aa1e87b9ed34a9aadee756540ca878015a0aa7b1157f6bd80a9fb2152f5fd86adfa9d0c60005051c002821eb012bc95d4a92a5e97a1c8af20b45c088330002880e5895af63d6f4fd3f43d84ac545c188931602002c2e3000a125800504fd63d3f63a3a14b0955f4fd86a87a3ec1543b,0x5d20a0f0287b0152ebfaa1e87b0d52f7225d959888db29fb9ea7bdd5757fd2f43aa4a8fb3d57eef06d00c3c18b00005080d43d4f53af2a87b41588955400282660014123580ac9561ab41584a97b5ebfa1e872234a5ebf22544078a1c005080c0028786bfc8e12df227ca5e9fb0958a92462c05602a1e87b0150e00283d6a1ec05602a1eff4b32b01002e08b95347458a9ab09000a095a87b3e87b01580ac15439102582a872e0ca5ec0560ab01580a8fa7ec656023a0c74140f280e5058074d8b92a5ec04b22a1d645612afd5a5479d2a50f602a3e87b9ed65579d0a54ea92b0153e5c285c1960ab3ec247439602ade872e0cb3559aa8fa7cb811d09090f921,0x1b012d2e0040226a1d524532b6912297f2e54068914a9aa7ec7573d1f4fa4ed5ed1eb6af2214b5c8831f40dbc1b4030f063c0a1c017081d43c0292723c44ab5295e8b9b1654b55b56b976a0156024de874bec556bd82ad255b911a59aa8f49d01e0005082c952afca878751788002048cab224540e95f22145415af53910650f43d2fc22a7ec2567d0e500888b1602b01580a87b01580800507dc00282064b43970200160e58ea9169475e8b22a5ec3543d80a874b53d84ac25612b0956f47c02ac1543ba09079207242c0a7eef5c551f43d1ea9aa1d5354bd2ebf2afd524a92b0d2a2af7a3eca45ca953daf4bd2e74b84418442947d1f4fd6f65277c8079090,0x5852f87e9c2359d33b10f3485e1f87e1ca7ca555ab48529c6ed8fd6f1e746b35a14215af0b50b342850a11b1436844447c88b910f220e4c08b08e05c0783304e258950e5aab7d5aa4a2d2e16d78b138594d5ce28ab0551f3516543d9e964050ec254bc84a8fa3cb85342543d0f02aa1e87e3cd933edcfc3d8e88012c2553d80b2d3e440885300028206a1c00505acaeaa1ec05742a1d53561a2c959caafa3ec1593d3f47d80a87a1f07e5ec1547d8cac0470096027786680c3e185c30786070c5c0a3d7f553c02a875ad1d9a50f73aa3ef758d5948bab0e852c8557d9e7459439d1e51f439406586ac3543d96888328f4a5c38ef44d0883d103a2223e445c889,0xe826a985d98fec2ccf10bcd5c42eb9a678d57b52e4314862f52c7295dcc1b583430301e601cc03180536007c81249c87310513b8826a2142cb2fd30b96184c739c1b4edee42e842427c84b908f210c4214b8010842100001f704250a17d24296882579b4b5db05100000a9a5bce10a38608ac85aa4215374ed44380876a2106919e08204905099533a905925772a292a6751861214625c3bb28595c3f0eeea49bfcbade90ad7e4e8548d0a1b405060050a100001f3050848820ca0910b081c412a8d99ee96214698e755cbcf0fd78a686caeccafe1f87e1ce74ab29c28d2b12b19bc78d48d4b94ad4858a15a90cd0a146a4685cb14368220c048d061e32fd214,0xe08002085829d70f22ea8dc1648d31c82686842acd04ad293ab0ab049332dfdf50e59c65e535c2aee13a772d4215a857422223e445c887910722065c005919e14a0cae18c5ddb33dd8a0a21570c318824a29db94210a53e3975b8e5b95094e6fba20a09f412e823d04320832e02b0690525feb1457b049452108a091d40c205d1ee18e529cbac8b4110e004000080c10a9000010300000c5a2343145784892ad1a4104ef9e549d8820b25425fbdc8508e03d512a092c80000bba2000036e2a10515d1b0d30cbf4a52152a41c000019fa180000838604538638d6a22c000008981e414625c3f3e0aa16570fc3f0e14295d797f946c52f3a5b950da0183001652c,0x8400582263a1c5451d02580aa75495c2a9fa9eaf3a7cadec35579d0658e581901a3a1ca7e80574b832c245c589771468282818580100042230526787aa31086a95838820bac7ce9bb8826b6854879cb8c7f2caeb470c3f559549e284214862bb09341212182c0000021f000009b834409200101db1dda9522b8c22e296976416882827d04ba08e41188218d80142800010b820008226487c83b4342102a6ec5e5ed3945d4ec2bb0872c3771428daa148380fd5300001330a4b595e0822490e48bf065337a137c58484b014200104be35c254000031607905d71bebe1fa70510b2b87e1f8f0611df9421e3f26ba42b51a14684296e16686d03030307002000041,0xe1458143d0f43d808005092d43d0f43d3ea822dd2f2ad8563aa3c005040d67aafed74a9a54951f6f911a11362a29376ae8062e0c2818b0287a1e87a1e87a1d2800a11da87b012ee8924bcab012be95656faaaa0d56125755af4baa495b56fd2ea8aa7ebfa7e8f4078002c24300040b596a4ae23ad4b3c005056c5022e1cb1159f63d5f4bd88a972214b015829291065888b810b81102e000b049c00284be002c19711762aa91860005114c002858e001411350e9430002848622043a0400742075baa87abc00507ed76a3a14b29582ac05622b1156f012778a68142e281c50f0287a1e87a1e874b602a1c005094d68aa1e8fb552a8af7a3e87b09580acfa5d5,0x6110653f47910a580ac154bd84ac0494b831d541a2803d0501ea028980002853e002c117582ad7a5ecf581580a87a1edc4740943d7f4bd6ea82a9ed7569ab0157f6fd96a87afe87bde9fa1ec3561a3a142234223c3a1cb0955e7429439d1a50f60ab0550f4fd1f602a1ec044408b687753068600ec0c07980a26052eb62007411b51eac257553e002822e58555e75f84519479dc63a923424243e485c907920a240e6c0a1e87a1e87b01000a12ba87a3d534beabfd554a92a3d5056f9d122be800504fd6925511d0e59caf7b5cb872c256323a0c4498001425750f57d0e0028246b7d53e456947aa2ae7a9d7b547d7ebda57958e8eb92bfb051702357405170a,0xe9ada8abfafe97a1e9fa3dd00c5c1848316050f002b0125b010016145800504ed76284113e9574b6a55153eb5574a92b9ca1561aa7d27ade874bd6d2e80f143800a12fa005002002c15b50ebd2bfe9f82d1d125d48005042cb2ab5550f63d1f53d3ef68fb1550fc0ab1911021702206c000a0afae54aa200441831dee5be4ea3b14b0954f63a11c000a1358005185d5ba30c580800b099c7408740800e8576001421f5e0ac754bd82ac0553d88a87abe8fa1dde25a048b8907123c02204001426b171a580aa7002c12350f67d1f43ad4ac054bdcf7b9d0250f6bd0f62aa5eef569582acfb7eb7b5eaf2e04a1e9fb0555f6b9d2e57e5c284409779d2655f439d0,0x2a1e87a1ec05602001428f50f4fd968005048d43d1ebcaa1d565639d0253f602a5c89328fa7d5f5602b5ce832c04445973d0e440953dbe76a962a3a0ca3ec5557d1e741960aabec14441943d828b8b2bfb01588a87b0550f6022e0474110722222458000282f6b01000a0818ebb2c0400282b65bd1d6e1da25909d289a11111f222e443c884910736050f43800a141a8f5ed5bcadfbb92be8e8129fb9150eb125ed2b0acd474e8443953d0f57d86ac154fd1e88b143800a13f8017058d7e2b055a0ac25692b3d55568a58d5df6ea5abaab7eb7a3ec045c094bba030b86070c2c0a1c00b09ed43a5000816711ae5cf6a24ded72204b5ee75552a895356aa55513,0x3a2223e445c8881f022858a00185fe000412f1d88d35aa2e1dd8561271e2fbf7bbc89a7161457df8f69cd15ffe84a2930e78cb8fe3f9f8bc78d8b551160e2474a39139ef3b8e8870ef99f145740018216b0d220810c630001842e3f15d8b1629e889851df44c08ec242983f1000e0b39c724900060a9a6b5e4c38e8a751212c0528eb471276955ba822c08604812c47075a41982b04fa08079007202c0001414f50f43ab8affb0156f57d0f439d4259a8e8115356fdaf662b1ce8f2a7a1ebfb1152f43dff439d1e54f73ddf43d80a973a443a0cb0150f6223a1cb1552e74185c18440953d0f53d3f43d0f60aa1ec04442943ba5834300760603cc049302c0560,0x66ddbb179fe3f87e1dd050180aaa6bfca4e3b5e4c6916ef0fef93165d69df779905b0970f602aaf842de85a1087a10742427c84c109721208c000141871ae6ca71e6b8fe223614d9ad7f0fe393a252f162d869f089bd134220f440e8888f9118222e444118000185668b7a23b11d89af8a6f29094579150fefbeef2ae7cd0515bf7dc9831ff6dd535e1ab05559bc7f1f602bba228b35116000108fcf3a9a0018226443819539e6da27443e4c26a42fe2a01d54d7f929cfe5f4244c08db9de1fcf9a4c58e3beee82359584b8f9b15f085bd0b4210f420e8484f909721207c0001c1873c0aeb8f60aaa57f888625c3f8e4c58f3d8a8d35cfc57c226f44d0883d10,0xc15e3d80b877411063c036f06d00c401878326221850c1965c1e22c58b17870a142c500042af70e00382867dddf37daf1f550f15d24492e3dc7267415135fc7d7f162c5e1e2a58b146cdf1787abebcbe3da78930a79e5bc53e1cbba02ca4809362930271e96ac5e1f878bc7d82bc049a1513026809d048189160cd1e0000c2b300161518ed4f7bae38abb166bacacf26a4bfee9f2613020533e2dd9b36ad5aa98280c08a001855ea1c00f0b9c7328bebc8482bdea2bcff126dcd04eff2edfb7f57cd8ad38d4410218c61430c17000185568b14fa469af2d3c68d7537e734971eec2b2d798a9773e6ba4a69a09c7f7e2f2f60a2afbfafc7aae9b7a1e40556c155,0xade15a0288050f0a4c08a00185de9b37877510006091a280060b9a6ba48d35748991b775dd04ebd58a166ffed3bd6bb78a7c7917c044c68d3b4f379f9b562f0ef806de0da0188030f064c0002c1633e89af5bd3cefbd51795be82cd34d3be4c79f79a48f93099d1b7ab342cd4c1106070f162c5000c2df458a00082fe000c16b0bc9db4f7a3bc8910e0435bf3551569ca79150d8a166d5909054410218c622800e16f9b739d000e0d9869da8ed4dff0e6923bd3ef60a9ae7f2fc7d577f976df87ab778fab15afb1515407835c7340a23811b69d1463cd69d02e22c5000c66f3ee67c5ebc99f1ef9b17878a9ba4cd9e79f021f021f3239e4df9c7cde5ead5a5e,0x59af814de29a05080a07144c08a000866e0af5a000c11300060f18d15fbbc2b8f3dcc773cd714573eeca69daf35df015a028e05160458b14003152c4d7935f734571eed23513c68003041ce3cd3ddbfe1e6f2e1429aabb740b88b162c58a001861e8adb800e0bf8f9557e73453e2a6fae4c39c3ddfde2fdf162f0f166cdbbefc58bcfd888f810f810f8f09891cf2604aff879ad7930a1f0271ed3c5d01110270fe029b779f6bec05766f82a2c57c0c6f18d030406038c26005a1f870a142c500082f71dc8f347fa3492af3787b5fb704d45f9e6f245458b746f8ed3f0f178fd3ceb4eb02efe6b5e4c287c0856ec5f01130254f153cbc84b8f1b152f1b43d0ef8,0xc3c58a00387668a4c084c0800982763e91beb9f26cc9bf39aab87e1e2d5f09794a2c5fbe6c58b362c5aaf3c58ae39f021f021f0e38fe79306580ac55e02b0534f149873a7ebfc144c0961aebdbfe3f87b05458af812de25a04880907124c0000c2931a089990d24d7bc2ac54d3bc0bc644c184c09ebb7e007824e6ddf505e20b54168820f0504fa09a412e823d045270387e1e2c58bc3800e19daebac9ff268c001c1a337e7aaf3e2b7fe723551a29a73597928dc560a6bc98738ff15780bc2556af5ee3c5e1fc251520e09fb0003048c6926bc9e71cfe1e29a0a6ddf254d9bc3c58b16abdf15c73e043e043e1473e6b7e4c2966aba7c59d7f8289813e769eec,0x45000c38700060c98fc4003831e3a51ac9df26ac3491f2613163bf16af88a6c54045f0145000c3b300060b98f64001826e3e91ae8df4fffff17cb4e3b5f751040863188bc3c58b])]),([0x1010020150261dac404010086130ed6080661c480a4080cc390814a00898756329404130e6ca52402261d94ca4f],[(1,(0:Int),22,[0x85a498208a3c0934092a08290828882308228821881a08190818881288118820d5c55447c6c26181618151810350261e604582c2610250c2005007c6e3c262a182898191824901490290c20a6111c111a11991092100d12668cc280c29468c9264921b41529250e2c0c06e58d49545562c61452c51c7035225125864a563560e72570d7857154b674980901086581f130803101a24ac260100623c900a46cc5c90164a8a13034cb1cc21830541118221252a8e89558a833970d04d91f9d110f186e0315a9917958a429984d8559114511d94828b154b9399199882865982c01311599150d92228a1135951543549144d0b92b9279891a15239259c15079a282,0x8a10aef10d0205c403881e025e1c2c0082143952850a142850a142a4162850a142850a142342858a7070851b43852bcee0e142142858a90b742d0e1787a1d2a42950b152e8201e401c80b002850a162851b5450a162858b142e90b2ac2c50a6bb8f752ef403e805d007a007404c00850a10842142850a142858a1428428c482842842d0e146bce1628d0ad785e1f87a1da70b14aa8130c8311428ce8314285c673958a742a10c1f082c58a7394e823143bef439cf1668541160431c070142850a3baafe870a53e0f14778d2684869443044191878d4513e181c69185012441244ca5ab18a62804a598624540460a4b0049804827c22349353d2809e060e008b0,0xb16280060cd829dd090577cae888cf6dcedda3cb71b43d0f53ba10101f202e403c80393002850a142850b14280020bfa872dc6852fc51543d0e6b8d1b3787e1f879a7628d8aa04c320c680b870a142850a17870a1740416285000413350f43c8e8694e28a29c295e54ad51a57f0f43852a9778168023e045c0878107025c0d01050b162850a142850a142850a16870a162850a3bab0170e1740414bf1511d8a162850a57872dc2f0e1687e1e2c52b4785]),(2,(-4:Int),38,[0x2c026ad2423e3430440e223822304114519058882a204920101a4c204a2078d42c204caa84a301a50985094642e682a612e6828680a62ae02e702e6a3023127918240e68687cd2583e32302920423068621006681c7886100c168620a820a420827c885c4848883c426848389430d160d0e050985290301864c468b05294f8445430302c6028d1143404f114d0940d10494441a059a191a218601838c0e34503d0c34441c1f345434523451342334093446341334163d691098121134260c0d180c248f34192097341c111f21072109241f056509f340c141f120f341a340328171097208f1817221f14474123406210f3411216de01a000f8017001e001c01a,0x79a28a0bc7951b16872b368f8b542a8130c83036a0a28a34d208c050a142850a2ba0bc3850a6ca0a74ffe1e68d35c6b4fc7d7ee8200c016d68082852dc2852a142851a14afd01052bcff0a74285e1ee858b43f0e162f0f43d0f16870a34285400517570e142850a142850a14ff0a142c5d39453bda7edc2d1ea03e405c80790071e005199050a142850a77858a1629be14a70bc3c529e87e1c2cde1f870b1429d50261906028535c5948231145e457852ddb70a342a10c058a678aca2a08b0218e0380a142f0fc385e1c7d414efa1de78b547221236d034d060a030527c30288a244a248c204c205c4051105098389438a460c448995012c0126010f4a023802,0xa220b1741557851a542166858a142f7f542b4fcb85a1e2a80f9017201e401c780162850a142850a176b4146b8e74564538a491850a16ad50a16ef0e142850bc3cd0a1787401d8ab79bc78529cd341429be8caf0e15314a8d2dee8dab162d51ae920d04038094284e8232229ce852a6829a7628d4862cda3e2d4e378742180004163154dcb7169208c00020998615d38d0b542850b34a750261906340414285d01050a30a0a73a0a63852dd473a5f95f1428d7401060050a14db416a850a5be82828aeb4145f8d29cdf0a178f0a142cd0b14a8de1e2d0f362c5400516d050a77859a2b22ba3a1a538575ccf1b4f8d501f202e403c8038f0028516d053bddf31cc,0xb7fa3bce852fea850b])]),([0x1],[(0,(0:Int),2,[0x12850852852a54a972a54a952d0f43a54a952a54a96874a96874a952a54bc386d5a4f1108828202830243593392992592392191990d90b9079059039c15915855835515495415115095a1181161145143109140d0011282]),(2,(4:Int),2,[0x4a96874b43a54a952a54a952a54a142952a54a952a58a152842952a54a9436860483e403e283e203e683868346832602e502e412e212e682868246822681c681a681410141012680c680a6808180868060c0408040c02020201ca2ac48c28a48895bc034001f002e003c016])]),([0x1],[(0,(13:Int),2,[0x50a142c50a152850a142c5e1c2850b942850a942850a10a1901050a142850c50864992992592392191991591190d90b9079059039019c15915835815515455435415315135115095055035d11a1189185161141121109104d1582]),(2,(17:Int),2,[0x10842854a962c5901450862c80a2c58b162c5901458b17405162c80a878a3b444344222422241214134243422281f241f201f141f121f111f109f101f3418301718173414341234113410340c340a340934063405340302023c01340103ede01a000f8017001e001c01a])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r11_ok : checkRowFull 6 [7,15,56] [63] [8,8,8,14,6,6] 2 31 [(0,1),(1,2),(4,5)] (forbUpTo 24) (RowSpec.lemma36 (-17:Int) (-5:Int) 1 31) [([0x345410208e4a840211c55084023629881046a5320108d2a642011710c40822d21900845943210089c42a8611348150c225882a18467453210082ea864201098d40841d29a89003a335210072c680420e54d04801c99a10803812],[(2,(-17:Int),2,[0x12a54b402a0150092a54a952a5084210c00a005002801400a0041b8d8e3538cc03a02a01a00afddb766bd5a7467cd97263c587060782])]),([0xd30236542765809b2a13b1c00d9509c3aa3190805e46243508c4c286a1185810d422a3129a04526153408a2c0a6811318950c22530aa1844960543088c6c0420e14d84801c19b10803802],[(0,(0:Int),2,[0x8428421cb962e0e1a1c31707a1c21801450c0092e0e10858b172f00b805c02e01700b80583e0f83e00b005c386e3334a4e253468db75dd372dc766d9763d6756d5753db26a9a2659725895a7058d535fddb766bd5a7467cd97263c587061a82])]),([0x1449d90084a4a22ec8240524917642102948a3b11aa14a249d84d50a50a2ec06a85248a7615432908ec2041109d8804220bb10804607643508a0eca681121d950c23244eca0425292176512029450bb290814802],[(0,(0:Int),17,[0x1cb802c015b286b5cbf074a10a1528ddb972854b172d0f17285e111e8874458010e00b0044a28b47d8e10c58a9c1e875a962a58a97078b152bc243d20e90b00396d25956f7f14210c54b87c5da10b1687a015578507a81d4160026b0058121a77b5e978847c21e1160028b28d9ace2e0f162e2e942e0f43954870ca20a5085b79bc58a8a6193489623880104a0122d00890109011284a01280448081c7960e1984444a3b6eacc241219faf4e6141428cd44a4850c4e0b84a268f46d7d1879c26170badb08c3dc6842a1c8e0c5935565694e65dcb5858615184c5b53de2631d924998974da2630d576899e6553243d2d82])]),([0x8080082143b25d008020418764ba008042810ec972010084c21d92f0210ec6a85210187612029040c3b1081490221d950ca51],[(1,(0:Int),14,[0x2152a50850a5220a4212004203c66178047821c00a142850a32a801231a10a1529422c10c703824044b002a6904305aa1caf0bc203d00e80b002142952854a2a2e1c2a52004201c0b552951bc023c10e045ca952850a10a882a1c257abd4a5422c10c703804570e1cb4fa50a10a9504c32184b40280125801254b06a49e2850bc386db7290c6239d0c25185061211308a13424cb1305061122303d44825a1a128626224cb62208481420c4c149516420c7723060a1428e89089c356dc143d4f46d9b55d17719040914dc8918042c391d1e5294881198b63d8a74c89274c491689976193282]),(2,(-5:Int),18,[0x384a04a1cda415291323bf142c80940f2038702878b142d0f43d0f4395022102214a45a3e6d9fa024d2fe12a1f414f008302878b43d0f43d0f43aa28bf9b36970a16685400590170eebd1f47f0fcfd1e8463870b212abd318b5787422c10c70389011a2a87a1dafc1fc04b4af504c3218901110211021502113e05a1eafa3e2c50bc3c51cc222250c2428889223e6d1a022608182e30a0f512184a6589e7275c9a025008c021808502262c3b848e0c242088821205081220448121cc26241ce06380cc073814a2110240da622449a647120a242479c421449c627129c465079c4c70a9c2670a0c28287889e3079c2c7111c6471a121e4279149bdc003c00e00e,0x9687a1f879012102210250e1ca6de8362856a939de1e405202ca5e1e879bc7bc220c03793da7f8f9055ffc3a9161168860860a0532])]),([0x1],[(0,(0:Int),10,[0x85901050a152f0f83e0e4baa1f87a1e2e809e85e5e404b68780105a1d9d01e8074082bc403e00f01b03870a1428a482f0f43f0fe1aabf87a1ead0ef080f403a02c08b43e8088813870aa820bc399fe02e3d10c452204e1ca8134c4162f2e1c5fa7483017405a020ba0233c2854a58081429d0245a1c297020ee622488921203080a2024d322284f112244481124440c102840921984818084a519517ad0037258a7910c16155b43d1b55d17405a243a1060411205372c49268990f26d8f74c40765d4f40948804d50802d2682])]),([0x1],[(0,(0:Int),2,[0x4210852c50854b972c00b2e00b00596870bc024b978051700410a1b284a2124848a13460854222050811205346d1744d0f42d0740d92629825294650912409c57050b82]),(2,(1:Int),2,[0x11439421421084210e50843c024b97805002cb97870e54a1a0104371218c871112447109a426509442490914270a0c287090a2428889224078a1e227881e6039c0c7029c081021c0670104047008402075c003c00e00e])]),([0x1],[(0,(31:Int),2,[0x183c58b152a5a0125a0150083972e00b2843802cba02ca1b0d9352d4746d1744d0f42d076498a619825494a51942489024050582])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r12_ok : checkRowFull 6 [15,23,39] [31,63,47,55] [10,10,10,8,8,8] 2 33 [(0,1),(1,2),(3,4),(4,5)] (forbUpTo 25) (RowSpec.simpleNeg3 21 (-7:Int) 0) [([0x26650c1484b1a32a460851c995130428d8ca9201946a654500ca32b2a4860518d95143028b2b1810a1459390084ca3316a46025194b5231028ac5a118094552d08c40a2caa264804e65323140273268a11813a32c94c409cc96482604e1d0d48402dc10821a83c12],[(2,(21:Int),8,[0xca142c5c1f07cb83e0f83e0f972e5cb972e56bd2c00901972e5cb152c00909438cb4db5434cb2d33432cb7c5f9178874a7517486cb6d16c86f99c06c693174a5d396c7191a6403a02a01a00afddb766bcd97262d5a7467c787060a82])]),([0xca22204c88e51348085911d9248a80b2239a49130164472c922402c88e51344481911c6165010b1a38d289210634749142ca420815124590841026144b1908206255081584a50ac842ac05284e3215602928598823114a351441188a491a6408c25295252046129227190a3014a645485180a4a948406c25294a520361292c4a109b014a625484d80a5128a284c518545042628c892920b14614941058a3222a480c518915140628c852918b14612940c58a2a148462c5144a4031628c84a918314622544c18a2a128460c514894130628c232810b14511900858a248c6042c512853120628a81a108314702106450950420c6a126084190c243b21a9080548a,0x92384481951d2c5090832a39551201264472],[(0,(0:Int),23,[0xec3028ed3212ae56112c7071c14685189458514944c50e1432503062598aa3142f4294154134015fbb6e5d2b846c9c1a6269c12684991258495122a4899223986a1140f59af569cda468d29389850e061471a3858c943150b142488fd0f50ed0cd0ad08507d03502d26c6a227013ae133848d122c48a522648712194889112388e23943743541d41b4094074bc71b036a5d74b0d263298e24388cc632164855214c21a20a16a12a11a8ce2c2258194174054034f8faf1487574ce599b2765caad556a9d5589e2c3b4a88b2366a4cb2911ad5490b842d1c6471892b26989c6822693c78a8e2c31c9b92f2cd69ce588e320d18da258b4c96540b914303c869382,0x4002c163680a2c5a5cafa1eaf2be87d0150fa026724b923c916005a1e87a1f878a16405202a1ca812878b142f80a87a1cc810c810afd2eb9f369729e87d05451ba12e1d9d42ea0f5058143d0f4385a1e2c80a40543c590150f4385a1e87a1e87a1cc8109d5387a1dcfa3ca892979ba026bca8319d22e90f485816020b43d0e1ca1ca94343d0f4386872604a1e872ad44a640983c80a4054bb8f353ff0578099e12f08f8458143d0f43d0e640864086c2a1c2858b43d0fa320b15a7a1e41520a6744ba23d116070e142c80a40543c590150e168734d50f43c80a87a1e9f2a0c3b60ab013117086391c73f43c58a19b3521c2da3e8744b14c2728b0c560e810e81,0x11740543d0f43d0e17878b202a1e40543f80ac04440943d0e4c0943d0e6408640864086408009833e8a1687adcffa3eed0fe026728b943ca16045a1c2c5a1e4052028b43d0f43f0fe02a1e87320432043204320])]),([0x1bb2390288143764720490086ec8ea080540dd91cc100a01bb238c201203764714402206ec8e88205405d91c9040a00bb238a08130176470c102402ec8e848054c1d91c8900a183b2388141230764710182260ec8e84205441d91c8840a083b238908131076470a102420ec8e81021d950d0301023b29920502047643240c0404eca628140809d90c5030100bb2982050201764304090202ec6408120205d8c41022040bb108206860a21505d8dad430490a80ec6d6a0c2485207636b122860990bb035a860c255081d8dab430512a820ec6d5a183085427636b506144290bb1b59828921041d8dad830922a620ec8d561449132107646ab061242103b1b58d2,0x1830a21085d8dad414490a20ec6d630a2482107636b428920aa1bb03591245050c9d81ad0a2182a82ec0d68490c15317606b422860a90bb035a892284c841d95ab830a22a640ec8d560c28942107636ac860c2a9883b135622860d4c81d85aa8922868642ec0d5c20210d5d91d240411abb23a280813576474301006aec8ec10214d1d91ca20411a3b2392408134764722810068ec8e8182114dd91d0184129bb23a02881537647404900a6ec8ea102150dd91c818412],[(0,(0:Int),111,[0x2260d292814cac3484d2224a9516131854c9831603334b02392b21c578d318ad678d931a2c5299a0c5830764d8971cb38e6ace028e32322830a59497ab50e14325071614704949834493b034c0a19348d60242c1c1a6940f9b5129c5252e0e3430b13d52cc99a162854c060f2eaa9130c199104a409902c41310605981c0ee010b7071c5850890d498d4c0898626189406d08300ca0d284c60d181888c14cccc0a90464165443960e05cc6c09546ca25121444a0357120a1414ad090c164ac09184251a1228482d6150a0624446033224489280c50a2c4489122240f309854890b84891528302923052a123448494a442d11387031166264e033814919011c02,0x84295280020a592a4c45a45c21a219e27105a14d28b6191c2b0cc6301a84c35180a3121c5680aaf1e8458218e0741b2131c460740e101c406901640d10326991e74698996273584b44944744543b43943743540b409405401481c20688167911e424509e3a10d1050fd0f50cd0c50bd0b501d00d7ec0905685284e84a83683282e82abb6ee1a3870b210aab8a8e193890e12303046ad3232a0ca4135325963419d5059e545849c5c50d15327051c18385151206d0ea57551c19518d52684f42342141f41d41341140f40d59b148c55291450139143010c28ba8a69204c5319302fa28a58e0b2a6482da8d9253488b132c28132041811a04d011c04a8134a8e0b,0x2909680aae79fd0138ef048f2438096870b1732417285185279ae56c6500aa1c584957a0a9016d4a2c90c7138264c37cc7a1cd452fd5e1c2d0e9874303d830e9f40f01985b9c2c8247970f3ad429428d6ab56b3c45e21f122607801085285c1d2c58b524575c38d671a11050abf94bddcd0bd49d6b4e9522c756618293b4ad3bd49f29ae94f60180ad2c1d47cb67a50a63d0f438d811259a12b002ea16a14a552e57a959cc2e60f30581438b6893583e1e9fe0e142d4ed7076b00a0a4a79a942e5a1deb3945ca1e50b003a4cdea5c7d2a8e55ea5522ca4e7247922559d12e88f44f812d2e5e9727c1f21527c5e310b3925c91e48b03072004086c0410842850,0x1f63e8aa4a4f3b432a010e045a1f87e1c005044ceead014a0a5b46ff6e6bc5684c3518191152dcdf1bdbba48a72214220458041818385ca17070a16284ba48f291d71ea9aa3cbfa9db7a3f879b190d51f27b426c36398c50e00084263695d422c3058a1e87a1d754002834e77057829c13e097047825c01d9152b7c29c88529fba73e828a78a3640415af0b21aa1de89604aa24d12245c0a50518287948c01d1480829b6a5547f98f36405a42d1950f6021a168f90534246122e90b024043ba1690590537e67c9a8c7a3ec70a564245f910650ea45864b0302b211be2921495d2dd28b0c5605446b214135e35a757c01805409ed20b478bca4245687a7c6d0fa,0x83a5083686b2e81551fcd811230945b61d1c00854a14001059c94211a151f949e257bb811446a33a53a4ef7a5180850d956e8ea34d24984a1087da8e1b654a0c458a1dd812c05a02d015808017056dd7974617024942172a171223221102411258a91992c35602b01170a2f0a170a23022f0a2258ba1410623522f1623023b16230258c911c2302580ac05602b3d2322580af25612bc618149051c9459a8458218e0702f23dc794d3854430a9a3fd24180a142800209f99c82e40f205805408540854084408540854085408440801182761450537c28d92153fa0a29cb72fe43463f2ff3daf43a1020c00b17870b202a1e87000411f45ebfd6414ad96a8f14d5,0x516f97d02a87bad6805212c3d28b2431c4e0a54f5bf95d5d4f43d7e12bb6c0410a946be0c080e023021a02000a0bf91830a05a1a965a8c442e0c2e1438244e048e248e2c76742e04b05270234220c000cc17f69cad6563a74444e14608c6c04581c4634362c4e243e0c2e0cf092322230673f3528c00160bd961565a82d71aac055500138946c487c1962a4604761c464446245e04b0117024f0233a25d12240b00e810041061c5c085c096025d9598948f0b85148b1a87238108810e85287821c2224ca0c4604be2c5e04b0133a45d22440b13c45e24440b029ace67a49950d5d1fd3c4a87172ad7a52972850a58dd2854acf2179038010858a14001058c18b,0x85408a4089408940800b85ee9410539c88308912445e0aa9eaf2a5785e3d5d020ecf017810104c00a142f0e1687a1cc810a810a810a810c810a810a810a8112811281002307ac30a1a2ea0bc3952be2256152fe022a24a7e8790933a05d02040b0240464086408540854085408540844084408940800283f6bffdf1b168cac45a22a1e970b43d0f3687a3ca8577053825c11008f022c50a000833ed010c89df2a5cd2911721ee74a8509811a112e891205801628400107fcf45344f2a3c8af3405756d1eb7c15a02d0528b6191c1502157a002a0a3b454b0e86045002018761e8d25402f5d76f17c9ebad8cac45642ca96c148c685702418011a3dd2fa3ec7a0,0xa1c2850b43d0e17404142d0e640854085408540864085408540])]),([0x204080150e1d9ad010200a650ecd64081004328766b404040298c3b3590202010c61d9ad010080a610ecd64080404308766b10202019043b358808100c421d9ac2040804210ecd681020454328766ac081012a18c3b35604080550c21d9aa81020286410ecd540808143108766a902040990843b35402],[(1,(0:Int),31,[0x114f17d0e1c1e284bfc1c2e5569ec0300214a10c5c1c300208787c1e8706506285bbe5bd0b426c36398c450690537c2e7a4e8458218e0708d06c32180d8d44280bb4244c79018d1110144030b0ec1c2c40909280c206140490118244420350d01e7120d080814c88080c8943018c84311092122104840a1014238106841110b013848a33c3423592232b0e22216484c09a8d1d3111cb956aa5543ac315224c4c28e1c32c4c052a40a502128e052818e0a2c2490a2224a1c2910a843448881060460512444ab8646cd548a564aa59333c0670310b448c981248c0512301913028490e4c248b38065090918502981842c09123030ca8499899113044a21506682,0x28f0fc1e5cb0a1809234e53c78d80160e1c1dc09204870020ba06931170868b69168864a65161164860860906b138a1d194cf020610208081e00421090027e69182c8ac00acf69c2d0e980151f43b382601200880478019a0a36ff5bdab17074855bb434ff54a116086381c066821065651a62850c4f10e0e14839c82040f2042b3a05d01e81b032e50843143b728af4a852159c21a7e2ddccda1e2946c577053825c11008f0025720a54f8e1a01450c008cf6a93d0eb69f8ad422c10c7038084210b903a86bd2a14ab59c82e40f205801628421084214a1083eb074a1084210a77d0e9cde870c50a30e0e1c1ddc15e0a704f825c11e0970034020b46b070a59,0x212004090027f28]),(2,(-7:Int),37,[0x8a942108421084210852874b5153188428f0fcb14dd6ad0a8408114701286214210ab1b90852ad4c42802bd6a4294070752a549d4a116182c84c3118b7946142862a58b162a4187a1a848ed9b9a8ade7273a18c872d9cb465610345949548699103240310067e81c21284052220dd53224897a96871938289d538240910238095b252a8910467d9104461c0468116042810884621148448110843810c8418104840a1060236ca9201490a39b09082c64c0a08182033120d0828446813804c812c0485812308941224a81140490124606060814a061428912180cc0928148893014a142150c0c112844c1814c06280c852226090915edc05e02700f805c01e01a,0x6aab6eae2f68490241c00842162059254d2f95a7fb98aa4d864b010ad24e9041634bd516c22c10c1409e470124040f502a98082040855074f00e812875204ca045e04a1f281287a1c88132c1200547d8eb54890b812a74604809140240096af0a170a2c0228120c0575110240c9a8d08890b892c04743850685c1898085c1894584592182182414c4e2004a922224b0d140270f64a502018143d0f43d0f43f80b28132b12af2a04220ca9e87b0151f20a262cb014828a813405a0ae3ec156022204480418044a84c08440960a2214d0d6828e832aa116086381c50ea82a1e87f09110653e44084408540844185c087009439d02221856950eaba6fd2d829700,0x8a40084008120048a10a50c105209a9b95a1a1e2e59b00280561f952a5684418017a4bb670028014])]),([0x1],[(0,(0:Int),24,[0x7207902c0e01400a0051707a01072d0fc3d0f83a2682372fd17921180826a874a092f688602756785a70c418a1c2a50b43c59dc2e0f96870b43842190540aa87e1e87a1c285285a3e296404178740301456414f70a9386871d4202071310603180a3029c085220c8830208881420488100911070110a440684044008d02421030260a14444911442051a320c46149327e49c87986ac549a8955222e7084e122014e22228481a2848b102c0881420449012448c0c1020844289013382424600d446c5540c280ca11124480a0818803180814202048092030a06101840328504892250c0a040c854204844a0814884080c40920188981130858302440a24605282,0x32e5a0178082f0fc3920270e1687a0150e5a681a5fed7e5624819002a1f2a4f0022ba0ae5e9f0a3020451020469e0050ba028b2029017beaefbb4b910a4dabe9790553e362f8082a03870a6aaaad385abc69d410c3038e1ec70b2a2a9d2d82a2d0e9413dc05e02700f805c01e01707902155d01e81076780bc03e03e0250840928707c6742952a5ca34a75a90a5084343b3903c810ace817407a05c00a5079064259fa9f43d0e93ab5ea5ca94ace41])]),([0x1],[(0,(0:Int),6,[0x14210852850a942a5059042977017809c03e017007805c00a952850a96c0597804972f0092a50b8020b4028b978500c250854a1421b088a2230849212060814204480c103080a10288092488a211850c12302828620ca394326649c9190f3054ca8950aa14418821c052890858284891822501682])]),([0x1],[(0,(0:Int),2,[0x42a50a54a14210a10e00b0058020a52004cb4020d0e10d444450983042c12285090898225061460494120a190650c9191b20640a8510620444684d0782])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r13_ok : checkRowFull 5 [7,27,29] [31] [12,12,12,8,8] 2 33 [(1,2),(3,4)] (forbUpTo 26) (RowSpec.simpleNeg3 3 (-1:Int) 0) [([0x710c40823a4320108e50c84023531420074cc90401cd41320072d08c401cf],[(2,(3:Int),2,[0x21cb9728421086b1c71c6cb931e2c3834c2])]),([0xd6080550cb1c1a190a8148a3052120654850c03264305210951504082325420108c55084022c5310208a94c804235],[(0,(0:Int),2,[0x80105ca172852854b83d00a805402a0160e1b1ba9c48e4ab3a33e6cb931e2c3837c2])]),([0x520204ca858940805950b11810832a1608ca204111329008442ca420114a084194cb0f],[(0,(0:Int),6,[0xa1e878a440844092b2ca142a74106f60dc0781300e81287a1e8728040850bc3c80ac0543d80a3ffa90c054204a1d08102d0e8409172c58a3a0520306ad972642ca2498514634bb994ca24734592c54cba6059890f7142920e2ae0c066280f82])]),([0x41044327654cc1024317654cc1014307654c900204eca58100805d94b0101083b29608276502129102eca24052105d94840a53],[(1,(0:Int),10,[0x12a50843c02e010a08abb4f006002082342e0f162d00a2d0e90c042142153c29425fbd43681d02c0c1f07c1d2d0082c58a53872c5a1e00583a55058646035224a240a406618467cdb1430910510630630a18a22ac552a571a5d94a6473490c48818a485522961c1a8b251382]),(2,(-1:Int),6,[0x8408142d0f43c50aefe5cb1541c18016405202adfea82c3230740814e812870a7409942858a3a07205309189149105203103311187147127136242ec18c503d491489288c500d740d80700e])]),([0x1],[(0,(0:Int),6,[0x2843162852872852c5449051af40d80700b002852850b9421b010508434020a93c54060290020438020c830829221120920819411110c10411809208a5c48a48c44944a30524c182e9343b891c8a432c512d160b821810851282])]),([0x1],[(0,(0:Int),2,[0xa15285085084343c00829002700b8049436225184946124526081041020821343a0d04c150a250082])]),([0x1],[(0,(0:Int),2,[0x84214a14a952920258082a5086944628c24a20c10c0820820410406a24521904f42])]),([0x1],[(0,(0:Int),2,[0x8628524044a1432082041041341b8944bc2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r14_ok : checkRowFull 7 [7,121,122,124] [127,123,125,126] [3,3,3,3,3,3,3] 1 13 [(0,1),(1,2),(3,4),(4,5),(5,6)] (forbUpTo 27) (RowSpec.simpleNeg3 6 (-9:Int) 12) [([0xb1013a58b62310272b16a46204e362d08c409d153ab09013a2974612027451e6c2404e8e2d8c8409c9c5a9908138b8b4321027454c402ca428a8c085948514b100b210a2930216421451c402c6428c2c4818c85145810b190930b12053212516042a6422c2c4810c84545810a190a2a52065120c52a40c82418a34818c4830c58831910518b1053220931620864418d14984081161831090070b1320200d16064240c8ca20411c4ca40211c2ca42011a8c820411a4c840211a2c84201198c62041194c64021192c64201168a82041164a84021162a84201158a62041154a64021152a642011388620411348640211328642011d11d4d8840b1c0bb2a10816106,0x1e380b1036544c788af150c189253a5b190096ba701026542c72e0402ca858e3c0841950b1b340813299635682016532c5cb0204c8658b56080590cb166c108321961e381025432c3a70402a865872e084150cb1c23aa3108162c474362102c704ec8a42058709d0d4840b160bb1a108161c175342102c581ec8642058703d50c840b1c22aa1031474455320628d88a8640c51d02d9440ca3605b2081945c0b5410328e58aa2c404eab15058809d36298],[(2,(6:Int),25,[0x701c74e48ebc3fa2aa29a28a24a23a22a1ea1da1ca18a17a16a15a14a12a0da0ca0ba07a06ae9c8743ca62c40a27a26a25a21a20a1fa1ba1aa19a13a11a10a0fa0ea0aa09a08a05a04ab11e5c4b56470d870d470cc70b470ac70783ea35a34a33a2fa2da2bad9a8b158b154b138b134b12c38a37a36a31a2ea2cad198d194d18cd138d12cd0b43aa39ae198e194e18ce154e14c3da3ca3ba32a30a5e5c9e5cc74ca72c9c79b01d00556dcf9300d768d797163b1fc0559b4070770ac373e06ce3c6e3c6cb84e7c741c791361ca61cb21cb41c3c1c6b1721c661ce11e41cca1caa1c9b1c61cac1c5a1c561ccc1c9d1d81c961cd41cb91e91e31d21c6d15c1c8d82,0xa142850a142b1438300214285e1f87e1c2850a14285e1f87e1f87e1f87e1f87e1c00704ac14e950a142850a16870850a142851a1428d0a142142850a8b0e0c0e1c2850a142850a142142850a1475514515c7850a34a850850850a346855c07060050a142850a142850a14695db853a5bf1e546852fc2956c07060050a142850a14624142852fcb78a3429d2dc28d085d01c180142850a142850a145941428b495842f00e0c008420c208426f850a142842850a14a70a753860284e954d180a2923a10a58c0529c2850a2a2471816d29a3471966cab64db2a1932c5a6343165ce179171c3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc3f0fc385e1f8779d0e8edc8e7c,0x285e1c2142f0fc3f0e142850a142f0fc3f0fc3f0fc3f0fc3f0fc3800e0cb92142850a1428469d0a142850a14285])]),([0xc409c2c19938813830317202005060e424088ec2041184ec4021182ec4201148ea2041144ea4021142ea4201128e82041124e84021122e84201118e62041114e64021112e6420114a543aa0b9026630e0ec60e42994c383a98390a64b0e0e860e42998a343b18b9026528d0ea62e40992a343a18b90265a301027542c3160420ea85854a0805d4cb0a541083a9960e19743120291a32e86420521c35cc408b4385b990096b262765021294c94ec60425268c5d50480a59300813b29631602017652c4c92ec6240521a2dcc840b5161bb10816a549763210292646ea4025a2c4dd0804b51a1bb100968b15741022d1526e84205a3869d0c084a51a2bb0811691e,0x325461450dd350c98b6437104ca3262d50dc4133152876517204cc62c1d901c853298b075407214cc52a1d905c81328c5875327104c93161d0c9c4132992ba88116b0e02107652c54a0204ec858a540805d90b14681083b21626481027632c4a90402ec6589320841d8cb0c98100baa1616281027532c1c30204e86583460805d0cb064c1083a19630076572102c500ec8e42058901d8dc840b0c03aa39081614075372102c180e86e4205864c5d50840a521831aa39468286453728e030ca86e51c00d9441ca3401b20839464036310728b006a820e51500d4c41ca2601a188394618362710272306a4e204e260d09],[(0,(0:Int),105,[0x6a85284685686284a83eb844668e07188728d6607244584416812aa49181f01e81a9929325230d421aa282603683282eb20e1c0b1b8f0b742a8268228ce632c338d308d290d0d65615261703ab2152c152a66c1618ac292324a300e80aa8c9261a2ba7157652724d64a723762aa28f5a0725071487375298508c55200500d571e671e76479925cc9d4e7c687cfd156146327b87b50393d38c4719af56ce5c395b31a9dc35931a49c8bda39a59879581c641c9c6bac478ab328b8a4b8cbb8b31950aa2722d3b243933b1a62719468870cd4e75a45a2a12f65454c5f4c8ae6cc635250a6b522e2258f2664b0d113514ddc91c51a515914b11d6226638621811702,0xa7b9d05e0ecc194324630c518630a1832c703c580ac05602b01580ac05602b01580ac05602a1c00b093c3988d2a0d0af550710290a991f106b21618aa0aaa8cc262916750eaa569749a88e87e88689288287686e89688a87287a9446bb42bb227ac289f23182298219814981318129811981cc51a8ce8ca8c68ae89eb032232822a821a81416141514133944d28b28a2a8ca303728a3180e180d180b0d68b68a685c705728c824262423241624152413300d0e28de8da8ba91c68490ee8ea8e68beb3d10f28c2b08f2c0e1c0e0fa9169128feb40b2c0b09e54e538f1a0d288d31132c1318f711619668a71a29134649a0f6a5672658e70d138c45a84284e85e8,0x72a1c0a1e871f92b8af7a5ea7a3eaf4b43d4e97ada3d2a5a7e8fb5d6d1f43d1ed687a1df4581cb07017e49687abc55557a7ed5adbf43d3ef69f4ad6877b43ad4b4fd2f47d2ef6977ca307461c0000410350f43aaea87bdd50416b72dca8da5e87abc295a5e870b4fd0e15f865e8cbc9907323c00a000820ea1c57416ef14954e5fd0f57d1f43e42d5f5697a1c2bf0d3d1a79340e687800028216a7c54477d0e168fb5c2d7f5fc5a1ced2e939db1c2be5283a50e0254a4b25a73d0e955fa1d292693f7b63a57d26074c1c04b43d0e14001041d43d0e4a254112697755e874a9ba26c14694fa7d2ace9ba25c5cf438ce90d60d4449243388f14fa16c2b84f06e2,0xea3d4f43d0e81f143af6a8f59d50f43d92acfb1ea7a1ecfa5e9fa3e8751e8f7b43d2f43d7efa1c0e3838143d0e3ca663621a155f4bd6ea82498f060000a0dd99a4184149edd3f43a7f4fd1e14278a1d76595695602b2150e5b8d37e87a1e87b3cad2e168fa1ec7afe87a1e87abe870af9160e2c3803baa1e87a1e87000817750eb5ad4f4ba4f5ba02874e92aaaff4a4ea59ec77a9ba549d27ead503e2875e550f43ac689d49687b9e97add2fafd2d0f53d0ed5f2341c687028700141034ff77def7fd0f43d0f4fa5a5ded3f4fd0f43d0f53d1ed56d1f43d1ed6874af9260e4c38143d0f43d0f43d0eb8aa5e8fade87a1e97a1e87adecfa1eafafeafa1e877c95,0xca807506c04b43a5a1e87a1e87a1c00a048c9687a1e9f4aac253d3f4b43dae9fa52592d49d5f6ad6874a956d0e93d0f43a5a1e87a3dfcc1f583e307b60f4c1e5803b036005a1e87a1e87a1e87a1e87a1e87a1cff416875b55829ffa1cafb9cb769caf8a54a73b4b858b4395a5e878b43cd0afe90fb21f243dc87a90f3201e41b0287a1e87a1e875f150eaf2a3d5d543d0f4fdaea9aa7e8fa1cafa1c28da1eb7a1e87a1e87a1e877f507da0f941ee83d5079a00f40d8143d0e002833e54550f43d6f5fd8f57d4f5b85a3e97a1c285a1e87a9e8fa1e87a1e977f607dc0f981ef03d6079c00f80d80bd2a1e875590b09af5a154e96cf241201254ab22812d4b4bd3,0xd3f63daf4fd0f4fd0efc38f471e4e0e031e0000a0fd8005045d4fdceaaaa7ef7a9e9fa1e877e497992921c58000283c6001412b57ebe27ca525061c0001433b2a495a56ba25c000a155a875792a0ac754d53f67a49c000a09badf43986718e16754fa16c2b83b06e2c05602a1ec05602a1e87b01580ac0560200143a354f73be4183830e050e952d0f43d0f43d0e9687a1e874a9687a1e87a1c00a058d602a1d2ad5ab6875ad2db05256abfade4c25a97d0e95ad3f53d3efe30fa61f0c3d987a30f2601cc1b0287a1e87a1e87a1e87a1e87a1c00a04dd602a1e87a5d62577a6e97a5f43d0e95edaeadaa3d6a5a9ea75b43d0f43d0f47bf943ea87c50f6a1e943,0x287000c20b2aca87a1e87a5e87a1e8755d16f5faaca87b1e9f8b4fd7e57d8f43d0f53d0f4bbe468300004081c482a1e87a1d594a7a4f4bd0f6fdef47d0f4bd9e95ed0f43ada1e975bdad4f47d1efa1c1c0c38143800a10182abca87a1e87a1d5145452557d8f53d2f43d6f5bdff53d1f57d0f47be4a8a830e050e1687000c1f350f16c71692b8ac76be973b47d1f57d0e6f850b368754155a7c6c5a3df458581870287a1c0010a0ca82a1e8733ebf37dbf35e971af3b9f53d0e3687a1e877e317962621c5800010516a1ec75ab55fa1c292c92a8ef6975b73d6ed6a7fb43a57e197932321c58147d4f43dcf53])]),([0x8088764340a020221d50d0250808143a1609102018742c11204210e858182040a1ccb0284100c399604882108732c24430ea2405244861d4840a510a0c6438724cc2242990e1c5328890a5438714cc850259421cd33050896538704ca830255021cd32848895438704cc418198c61c932444854328704cc2240d9021c532889035408714c8c130e62405214261cc840a520c096408734ca2241950a1c532485064328714c91120d0c61c133120c3b0901490890aa650e0990c0e1c804b50a0c3b10814860a87302129060b0e2045a28461d0480a40a1c80422121c40822141c39081692228750212912230e842052030e42011284a1d0084a512143b010948de,0x5030518ca1d132c0c145328744cd030458c21d132c0c115308744ca8303150a1cd3320c0a6418734ca830295061cd33091066528714cc428199061c93290a065418724cc2241990a1c532906065318724c9418190c61c932885065328714cc428159021c932906055308724c9418150c21c933044856328704cc1220d9061c132848835418704cc2140d8c21c532885035308714c92140d0c21c533044836318704ca1120d4c61c1334080863487473020214d21d1d20808643874728202150e1d1d00],[(0,(0:Int),261,[0xf0687148d129a22f51e54c5f3210311061101510231043102a12621e18ed112520c311a251a1316141c341c49ab688208c20881c642ca40c3d48498448c8489938f247708d2a0d222626446f574a0642522332222c49164852442c640e2a2a6026182c4a8d80e16c42444644e60485448604858a23c48709450c838b11711e118a208c38a82462244a704660a0388a64911585084b092504714a645250d1144701d14f9a0388c5914c0e0388cd110f9487894c0a8a0a2b3130963303921301988f2415241426290d46495190f2a0f1295130e24870cc4e4534720f0b4680b262a31465071219121a2b8f2345b8f14461c6407338f30c5a0f304584684429702,0x501800aa29c3418282830548668443c242c60342c28262853d8ea8a49060a0985090c0c118181c9518f5d9592c38a214c10c911838649928939862c1798c30541c30389478481cc82024384460340cc40ca61c581ca21c88bc8e3cdd7a0ac158f0c464c63af2a0e150626061114168f23931416190a248a1829182c22af260514871885309430140c13239f180b2414b0c33960af733410491a1310510621264154111a331643324f264336331e0eed11a451244eca0c620c0e0e2c1a5114648e114130e690e518a338320e448c55046eace9ce93cd696609e7c4a20a220a420640c520c86ac8c88d12058904928495038b0313a113111321462190a8d128f16,0x718271810c509527a7241b2b0811467281a0d25a82294271d249c251d158701681aa39b29c616588b0587239723b1300324832518109a2228141403282a99872392120d01e956628d0e1a0a642e888b1111026962a01280eaa26304c1806249823ae022aa46231182a326128c42ba72b0f2399190616051b0a231c2649188a0cd690e03a836920a232e2217218712f7e5530f0c8a23b725151a0b2326240514e4d66a8726762a51a8714852a05223224c323181946198189f03e95451870a87228f0a0d290c310c292528d5a461e651b280d2a0813083f681268162a0648063106300621382f2801576242431926242a24463c868801a519c8584e5cc5849914,0xb299890c060468d0927940baa38d20a90429809246518909689674c4c3618f24a225222a2722343075a777270a68bea39830512a1e1e1e141e2c9a29182218138d0aa948c0aea297170f1b0f260d233628a322b01ba930061e36323018232a0b1b8a0b68b8f242539b24f549728c3320630d6b4721a7170718871b070c2a39c0c6a4120a28c8b22a9232a180a160a16260c0522b532051b8c28052ab7180e1a8c3049300522a7328d328f2a8d09e89a98d63a71a053277164e0516469073154294406473942a181c9f2898288c220d188c2295098f228c05c5376a558c70e5966a0a230a300a271e279b259b20a81098251f261a1318124551614950c0d04061,0xb12996138f457be800f051c38078004c19313323c89e9536c14a08c8362132c2307d187df87cc8003820eaa7880d05e85a856880e080b21171615150f209f1a171097209b2d16148f07687286e86a8668629094251c241c09288ea59f249b272c0e0e12870b070ce8d2a91c2c9d2c1d210734180da8d6894661e2913190e261d19982c92211e289a1099259925192527249a229227af232724a525290b0809c452b10804a84ea12f090f23ac231322647a87ea2090c03162924c41593290b220a086a3ab298b21a8239a25930a5698e08a8829826304a2846320b22b71814300c0c8313933083318f292723161a07165540328c8250c0ca979f159f159b10920,0xaa823953aa93fd6e826837213511a84cc379ca32144f2898511ca17942c284e501ca0a0f14767a44c488e9111203a4241e48309250f11107a20c05503870bc380040f5928428669f892c59a94208503c86ad3e741a1f7d1f1645e1c3c7f0fc3f8fc02c850fcf43abbc3f1f34383a5e1ca7db162c5e5ec05c3d0e4c084c084c089131c39fe8ea4000820e345058a007825677939b28f7c18f431e46038c1e2837213511a48d42661b28d8c4df0cc050850a1400107bc10a143c435208be828508b682145142820a73db0853b4690badda18c630a14ff1810627fa05c3a29df4003828e0c8a324d8a4cb0ac450a0008846002427b50f43d0e81b0001822650c645,0x700800807ec952a5000812f25e95294692f8011488bd4b793caffadd575b4f85ac04a877b4bf009f831e8606070c0a3c04a1a1e8700001f750e92452d5bd0528040a9eafa4a94ab44ca7abf800408b9470a9fa8f2daf49da0dc84d44661b28d8c4d70cc2500141f700040918002057c57a001415324eb5564863000283ee00081cf14a8005099ca7a4e8c30940050bcc5d185de94397322a6a97569359fcb11301400007ec14000044c10bd00000cbb18ca8164cc114f90a0e1438094210a00003de0a10a5b876821420a10a518503c8145ef5855843ac2a56729c2bbb6163109d6bd2a58afe30fa61f0c3d987a30f2601cc1b02280060fb8003071c000828e9,0x542aa23491986ca3678a600010a3c4ca1711d49451926c712c45000c10f0d40b863f829e853c8a07143c6718ca319062b8c5518a8311c6228c37186a30d06138c25182e3054606070c573946528c8511ca229444284e5094a1214140e281451d8e911522224240e4814925f911ea22207440a16a0254b43a54a96c0543801010792800a08d92a54a952fa1ca54956b5a1d2ad5fd51eb7a5a94954a8249c9049687abd5a5b0540696d809fcc1f183db07a60f2c0c039805360000410996b5000811325e15252a52d4a4fa4b43abe974497ad5dea74ddaa4f43d7f43aaf43d3e14b43d0f612b0124eb6004fe30f861ecc3d187930301c6029b0380496005002801,0x3bc6850a16eb8e16b7a1c50454ac50a54a857e14141e28285038a0526005000434f0ee86343aa2a3423a11d69c2850a538533caf544692330d946cf14c00020ab8001057c302000417314efb8b286a8a324d8e2580a332000416b1c2aabbe5f95f74bf1a3428d0af90a0e143801400107fc162c58b202a1c00104bc146f45464534a729cdb43020ad3b7e539ae9b79b20269e2d3edb96e53c59b142d5e5c2c59b43858a550e48487890a160450a00082563fc6043326dcdc43420b0cff8a5f9d8a36ac5aad3c52a16b78a77b7f366851a55f851e4a0394141e2828980000843e0850c5000411b04cf1950535ce8ac82c51851d3953cee39d0aa8668d2a14d767,0xa7914141c2830f002850a9421000c2171ff5f95149245e4145946ca0a3427dcf78aefc539e22a271c28cc8cf765b858b36a853aebb41b909a88cc36313149ae158000417b19e14f752461926228002109800315ec8c306632750c60ed4a28c322c4fc8e1475a46fa0c0e183812020a002842618d0d082858b4397e3423a14af175050b145c4142c53550a08a731c6956dc69d8adf97e15a70b542c56dcb72a14a8d2b57973b2020b142c50afd30f861e4c0c0f18144c0000420734e162c808d343b20a7828adb8c09b729cdb430aaa679ce29a29e404d3853b4394e539ae342cde1e28d8a162c50a75243c4850905160000a10182d2e6f800210785940018336,0x142862c54c80a40415f831e4606070c0c3c08a162850a142850a001845e0a14257aff1aa4c5372bc28d195052dc2b4ecc144e78ba8d043122ff5b335cb70a34e8d08d0b96a542c58a94af0e96ed1f2027eb07c60f6c1e983cb0300e6018d8f429e45138a2414141c98a3631314997158901000611b95d436a0a56404ef9cc9694145e46e217d056fce8c2b87aaef8d1b15a78b36aa5a3c2168f9013f123ca4240e48187803b23c90c2800104ac346b5f22a3b14b70a14cf0a34514fc28f2505078a0a140e4c08a1400308bc1400304cc16494ef96e00082462dcdd4f78ae8cf3dccfabcbf33cbfaad3d52fdd742980a5f80060c587e5c38687e1d285905457d0,0x1213d8d7000412357e00182e60a3ca18915e6fa2fe87aae78d2fca7aa146a66c8096e28d85190a27144c285c50b0a0a0e14aa7244c488890907120c24efa44f2888839106015032858a142850a00084be0a15b715d1cf3629ca9980020838a7149050a5799f27231cd04538b2aa97e35ef77fed5da6a28b142850a10b14ef1f478da1f87e1dfa61f0c3d987a30f2606038c06360000e08385241aa9b14cf91534e74b72fc2950a538da3c2c529df449e49090f1218241c980164041640414001094c345243daefc594349746921952fe5b95e75a1450d28e950b55b7f5e2a12c05000424f4808af1a6fa000422b052fdc79390b2aaa46b467c5169451451d0a,0x6e15b735e29d2a57c591951ed78573cbfaa142850a742950a15f849e890392121e242498000383961590b68d0553b6e5798e55af0a57851a166b9f4bd59a56296e5b95f74bf7e147a280e505078a0926050e00005260750e882849d42e20a7328a28234118e30a1a11d39d1aff14a858a346aae14a7544692328d96298000419300020a19451926c712c00020d1922d862381c9458aff9c09ef1b16405c3f0e90702ba0004143205c5181b120200245b73f04bd0979120e24780140010a5c538012113acf0a6f9be8a79a91ef28a00041073be1668d2afc18f230380142c50b140070a3cd38a487641669fe000828e19118e72a1e11d77cc73dd28d8c4c70cc0,0xe53b4e342e42b5e14294e63c56686303ba000815700000a3861514694e28a8a84b0000829637cc73bd1ae2ea2dea9ee5fcd44580024287000217f87c43452428a7bcd3554d94df95e362c80a87a1d12141c287000070a1c1687000c14f4808a71890a6a4047126de69fef78d1a9551bc3b9e6794e34296e68a31cb72a6e2739161229e45248a3912f2252449c88391111e22ecf4292851d0a0a10742423c84490ca1e0a08f411205a0000214782c500141e70aa8624142c52b1429ce55e79010d0a746852ad797f142fef2028af3c52dcd731ce85e9ea97e5f85a1ca8d1b54a96f1428d6fc2854391111e22245807228b345e414294e5795ee3852a73c53b679,0x71410b08a9dfcbc5e5c694f3429d2b55cf8b166858a5bdde1dbf9ad3950a55a70a362cd8a5bc50a3668d8b2029014809fca1f143d28281e5024981202000427f05e3c003056d54a73fc63457bde2e2b9ca9ae34a94f168f1511537e2c8482b5e34698f34ff29caf6dc6c52bee95e342dd0b146958a74b77e227a44443488491052604500042570d0865467b5e5f8dbde40514e8d7dcbf33ca9cf20229e294e14ad5e6bc51a16a958bdbbf093d12121a24244829300001054d2ea1750508ec496a95e5f8a29af2fe68a29af2fce9af54e9fe5bc51a6bbf8c3e187a3030246038c052e005000427f50f2022a00483beba2a2e5cbf38115ddcf733c624741b47fb9,0x94e1428d31e2b5e5ba4e959a12df25ba4285c842cd0b5cad8b47cd0f2f16a85a1d223c44488861600500243f71defcf04b421911d1695533c28537cdf2bc6b5e12dc6d5ba539daa538529caf2a34af4b2128a762bf0a0a0f1412281c78029a000c1df2455414524352dfb5e29a89518538edfbb0857e187a3030246038c06260000019f8000073d11c953c63121611ee68a53cb70cd2a96fd9ad0a53aa2330d8e3180004147030854412a15518e54b769c5049524651b1c530352514649b1c470000877638d2b9bc7a8630c8700008276165212c0c6a5743327be68228dc4e394e5641515f4181c3070000309dc142c80800905cd14774362c88860454a733ca,0x8b162f0f140030a2dc3c58a00182467a93deeb2e1dd75c7c577db779539eee275970ed7cd7bf8769cbfe3f97260cf1e2bafc3f1fc7f1fc3f1eaeacd514649b14996158000c3ab0ca9bfc7fb750c645b1299613f9060e0c38143c80a280022018ac6f978e09b7882e82a4ab535c91510a2c24a1e5cdf901457fe1b51a34bf8a6385bb2023b142c7ed3ad0b74c79a152842f1e566c80a877d12121e24244838f0240400085061a6bc84800304dc6bbe08299e678a28eb6eeea2bc5b46f9d6dee98ef78468529eeb5e53cd29da79a34a98f55a72be874936bc894912722223c44308ba8479089210c9c0000414f65e8e23421a10d15d1af2020a5795341257f69da,0x47f307d60f8c1e983cb0300e600cd8143d8080050edd662b115eebea57111425fe00582be2e44b21582ac2547d84acc5602b19580ad7a1e8fb1552e44194f970650e941e28305018b02fc4b82545580aef55150f4bda69564b82b0154f60abdda0db08d44692330d946d714c58080110bbc0028206001410b58f43c40800505ac0040306a1eb7a7df831e863c8c0c063c080150f43801014fac04b7dda800504bca5294b92eacf82928f53c22953569ab45582ab7abcba32bfb4525b1953e968fb0155f43d6ed6c44d06e426a23491986ca363136c330bf2b5d5f480050d5d7f9d461888d1d0e5d8acf4bd18bc48b39d325808b992d35612b9553f7570631602,0xc49f4dfbca72a158eac746c2b4573e7ca69c9b326ddd9e697edbf1f96ddb729e6c5e1f87c1e212ddf891e52120b2414480c980143c3c52604ca10c5c1f00400105ce880040b5b8777cd14b799ceeb8b2aa7efec34fff8f14e7a3dd04df822b8f39938f67d3e15b769f078b6f57c05c7c59a89304c0800988b69ae8229c244e7bc48da44c587c2bad39a281f5c62e9ecffb83958b60a26047e0a7a14141c2818f1f8c3e987c30f461e4c0c0718066c0a1e2d0f43d8080170b0d47c8095755785b3df7b7dd8543bef73d8a8c832870a754947c00953543d2eaea5952bca05476e98f61a2e9c6becf3204afca7abe8fe1ec056021b4bd868b8126c5a1f41561a220,0x907260001e0c1bc726247dce0468a8a6fa6fcd45f3ba8aa9aea6f7ed3c58a53b6fc3dde3da79bcbb7f562cdf3e2f2f35a7b014de1daf9bc3d809fc61f0c3d181812301c60197026bae8724f7d9a8e344c29c79b29a76dddf436af6f15af9bc7f0f378f8adff3f36c1515ef6df978adbbf0a3d141416282450193022801e18dac056c2000c117130655395453ad1a0bbfe1fb735170f15e737d34fa02d0178caa9a28e355ff2fc38de1f878bc7cd69f8f6be6f0f150a6000705fc6e200042573ee772ebcdf5ebb6e8630342391212c000610dbdf6fd1460981098100030c5c6c22604004c20f00060f9800305ad35cff0171fe0a8afc12f22424384831e045000,0xd48d057fd54bc785caac9511a48cc3651b3c53000182e659cea8a324d8e258000c10700080dd8ff8aa18c8b6388e0d0515d726943cd5de1f8f3dfcf3990df0158090c60fd4001876e407a08c83638860981229302002625580030acd34003059c6f2eafe10fa21f043d887a10f2201c41b022801e191a2d92a6930200160a589811e73b94de9ce44eb2abebcd7411b4a2b4fe428bc39a09d76df978b60aaadfdd73f878b17979b162cdabc3f6f362f0efe50f8a1e941409280e500cb80001862e2604261c000c17b453a11a29df395458adf9a8b877bcd15e027bc9990d1515cfe3dbf69c9811afb1d36f762b5fc3f2f166c5abe129bc3c57e127a24243c4848,0x471250c645b1c4700018556e1ced47028a70a7bde24f7b4eebb4e702f09780b8fa09260783022c5000c31f70f162c59a70a001c1170006093b87ab34d85762f0e6aa6fec04d793564daaf3f0fcf93265de1eef8f65a2be6f82aad5f9e6f2ed3c57bec05cbc5f09580a285a014d4391111e22205801787000432750e142cd2a00083061f1557a11c89b76fdbf2be2850857bf8775dbf9a2aa2ff444542931618f17c354bfce1687d014d8ba12d0151f4028a150e484878908160458b1400309fd14fd476a8b356b8fd3f0eebb9ed7b9ed79de7ece46da6bc3c59b17c256028b16805162a1ca0a0f14102c00a50b9628004195820008586261451610d0a697ee38,0x62c5e1e2f0f162dd002c2137e4ae2514dd5cbc5ba4c684c396226beebff549a138f8adfd82aadde1f8f6fc98d387f1e2b7ed7c579dcfe7d0e4444407022c5000c33b457dc007052ce7800608fb973511a68e1517c15c3bae4c88db9a0b8f34945aad3d5e3df775e2930671f179f69fc85e7d59b56a93121302780930142028385160458a4c080078666f0137e00185463551ac8e15178f8a6ca8b35f7f9e6d8caab7eedae1c9871ff77921ca03022c58b162f0e001863e8bc3b7f69a35945001c1f71a88e747fa6dcdc4dbbeeffcd6fdc7bbc3bafe02f01214c45000c31f70e001838e3e5000e0a38df468235139edff0fe7930634ee79ccb9f40b83b91c28eb,0x78b15ffb0555265ce3f8769e2b6f65a2beef2edfb7f36c14d7c575ead80b978be0a8be028b17879a911e222c44408871e000061a3a2db68981001305ddc39fe8007069d162bffc3c57dfb78a69a39dbf9b56acdefdf78be128be0a2604f0145e1f879a921e242c48409071e070e00283ce1f11da8554f78aa8bf79daf7bfa756d1ff53d2e2a26fe2f82b405cbf0f35301c60187022c58a0018746000c2b71b8a6800e083a2b7e7920a68234d71ed3f5ef3dd544661b1c630001865e3852923451946c93678960003127c68a000c13b1bc9431916c711c000625790a609cd229baa2bdeefddb1d34fdfb6e292e5f9739d25f017809100c1c18700981000f0ced1,0x2293021302130245e1e4041787f0170fc3c58a149810981098109810f8100190dcce3c59a2c25b52c8a8f8a7dae1e6bee6ba9054554936edbd58bebc828a7b3eabcf43fdfa0a90551edf9d0b366dde1fb7f3f87e9fa7ede2b4f17efa1cb7f014da0921c8080f10102c08bc380061abaabfed380060ddaf35c3baf4397e6ba9b15dd5c3d809af26ac8b35d7e7f878b15cfbbc7f2f37c7e1da76bcec569eafe1c99726d8e9d769f978be0af01780b87e1f879a941628205018b00981098100030d7df3f8e800309ec6ca34935e6f27dde])]),([0x80400b204c3a6501002a8130e99080040a61cb0080100cc39600802109872c020330e42052404042a1cc3a64201987120291010050c261d333],[(1,(0:Int),67,[0x180a43200a0c21264a8d218311a03ce09244686046504e415442524150700e540e4a0e0b0e213006ec8a898c2264542508c09ec4ac14a06300c44448a0c82844838c814c214221c380448688c48c81c1a1c459861c391a3135125189d15917945515d691d1160144450a8049404920cc804a404680434044c30487082508894311c41c824c8228c3123549d991821c6318498282848284a3c64044624222c9214291823042504254901c301c981c621cc518684611c91a91e11b112230511a01cc21c45184908254a119117118430845088442234a21c331c115518624c01ca518248651531591601c84248290891c00c2228500c2c38424850148a24491f282,0x5180004153214c1981b519e2ba3a3904641b1099611822c086380e09154e286ac59a7a593199c131c209b298a20a223a1130e33972bb41f468884a814c63c8ea09a90868caa3caa284c4886882a1c48488648141c181ca20c8838a40c4228421ca00c859a2143d012901310118806900a88070805880b080a91d7909408099096125313d6858845219090f111c11991a0f080b090a110f29cf080924952b8f190f2acd27a62496150e0509130816060806288f129914568d4ac4c130c1521302132119a24a102f64c5210729661210b451e48e58546c64c228763762f4974777066566954987288b2222138f108f220a221604870a7650309651910746284620,0x850aeb8a886850a57870b7bc50b742f1e34299ed78da1c2852ad7c5e5ee850a142850b142851a36e850b142f0efc28f451e4a03941e0450a14594578d14d05e5caf37ca72a14294e1628d8bcf852b3468d29c2c58b162850b142c57f287d50f8a1ed43d2879500ea0d80142850f0e108da82850a142f0e542170709ce142f0e14ac5c7dd0414af0eb75d0f438533e872a5f853ad7d0e14d50a562be4183830e00b08c78a5bc50a36e96f14694e35fc61f4c3e187b30f461e4c0398360050a142c50a14210842c50a32a0a1421a1c22820a14285cb142f0e69a0b43c50a28a0a6f850a5b95e14d78c54318149450a14c78b5fbbe63a1430658e07819d15e14e74,0xc4ed3f7ed5a78b552c569dd0419c8279047205e409c80390101e20ecf4090811d003a0201e4128780803d00400681c3c58b1787e1e2c58b14003041cd7c58ad7c58af9a18d22292b7f178fc5e2d5579027200e40407883a1d0100f20107c08a1c01062c5a1c3c020e54b162852862850a54b1450a57dcd540eac3e2a5ee3c5cadff94a317878bc3d5bb146c54b4f179fe1d106229da8d04e9a7fdd72deabced7d58b162b7fe02f1d3bfc3b4f55207f843e887c10f621e843c8807106c00a146b4142850bc3850a6b8a282952df870b77850a169f0b34a97e142d52a37870a146c52bf87a3da70b142958a1428d1b746c50b15f831e863c8c07183c00a36ae1c2,0x85c1cead3b95431864383b0f1a529c5445bf1e3522a91302a215d04b7aa7fad2bdfc21f043d08080e10049801080020a1a29d0a145745398e10a54df4dc294684b767b5a9d5a91aad98d4de2a4294e149d8a52b75f889e91110722023c08a1000013f054a34a4a12dc104565bb6dc69ce343362ab5794696bc285f911ea2220744023c00852800009db2f0e14d85ff84ff8dc29de36e850a8c6ab3fea851b5ecca748988a000027e0acf18b281350eda46743559d085116022ca0a14124cf87e1c298e53c4af1a5b85b1c2a50463684345848c5e455a24a08c8363886000d062c33a00041073ee5477c02f405e4083811e0458b16280060998003044c68a8aff,0x478d488c10181c02bc61455a70611fe5b99e5b950a578539d267b08fa1194230845d088a10f4212841d080a3002850b14000064c63838ac242aac850a14c70a63850a34294e178f2fcafbeac296f546950a90b05b82286746399e6394e54af0a8410430cc680800d06ac2ea16d1ac8ef31cbf2a538dba142c8e552e204440808080e1004215fc41f083d10100e2005581142850b43858a00082a60a1668e68e71a5f8549de1429d29f8f37e6951a16a8d2a166850b43950850a14eb107a209440e2c00b0f1c468d0a09a2a29271ce71aac6abc894912722223c44388ba8479088210e8c0084000051c1468d282131d5c3061250b10a8f0f37d18d3a346846842,0xb142d0e000837ed0d0b6ac05578aa828d0a1428dba6bc50a142853a178f2fcaf1ed7c52a5b9d4a36a850b]),(2,(-9:Int),13,[0xc680b405174047421d0551011900b100a8a2288c084c11488283084d090c1089108890480c8188cc084a910a0a49898810c78a8709469446048595040d225890d1a0b09071216288f0b8f208c1288212a21942094300f128f118c0b8a228921091907260614061085121918831607111c10940e0728c4cc621105072124210c088b11892a07280618850c4623120a12191108c150314c6294108d138c173630184c504920311130c0612019094904c044514879c039a22e238839843980392439923403980196232a311289090484890a95079303905409099103868384438a019187104512038c0392029802909408838d37e00fa01f003d807a00f2001c01e,0xa142800209b82858b1429be546dd73c2859ae820ce413c823902f204e40407880710767a048408e808079007209600f4010801c0340e1e2c50a142c58b162850a162850a14285a1c2c50bbaa2ddef3a5fcd8b16aa4078808100e2c00a16870a142858a142850b43858a142850a15e14162850b14504746858b56e850a906c310c050a14624142850a142858a142f1e14a73b74685ba1520620383002850a14394214210850c50850842850a156f0a142858a14285a1e2850a162a50842a50c50b142152c5e1e2858b83a82320d884cb08])]),([0x1],[(0,(0:Int),14,[0x5952557e9f4ab7104e205c404070855390100e20ea00e8c04a952a50a9528c492d0f43d0f43d0f43d1f43a55aa08c320c2b892a5a1e87bbdfc01f403e007b00f401e400380360254a952a5801258015809d4543d0f43a5a1eaf4ab56bf00bd0179020e0478143d0f43d0e96874b602a1d2d0e9687a1e87a1d104b52a08b0218e038b1e87a1e87a1e87801254ab5006128e2024442055182488438882c441c421c100c1018331849c888888842220401c41d11d09905941189d83d45d25d0bd199119079815415215c11a119116911310dd22308838c01ca01c901c8228681c121c61148402913115118118e402228243084842882])]),([0x1],[(0,(12:Int),6,[0x84210842108421083e9fc01f403e007b00f401e40038036005ca142850a142850a15285cb142842e5096e14a10a00c050a142850a94210868908809080888084805080484048403040282224182420181418401483d81d43d23d13d0dd0bd09d499299259099079059039455215155115035191611a11c113115119112114118918511d82])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r15_ok : checkRowFull 6 [7,57,59] [63] [7,7,4,4,4,4] 1 18 [(3,4),(4,5)] (forbUpTo 28) (RowSpec.simpleNeg3 3 (-5:Int) 12) [([0x382105430c78a8624012d1504082392a10084715421008d8a620411a94c804234a9908045c4310208b48640211650c840237],[(2,(3:Int),2,[0x12852c5ca972a5a1c2d80a2d80a87a1ec0543d0f602a1e871dcca4cb1caa726930e4a38b0e2a3870e1a395a7467cd97263c587060582])]),([0x3161418d0b54b0a0c865ad301026542c38c081321961a6080590cb0cb0420c865891944082313290084616521008a8c8204114990804228b2108044c631020894c640211258c84023f],[(0,(0:Int),6,[0x10843942850b9428be92e57b61cb01d8160050a14a142e50a16870b9728514923180a16870b00280150e142c00a870b43d0f43858b1437191a647951c54593db766bd5a769898547831c0c6031c6d1a1ed322ce4b62b8ad2b2a6ae8a98e58cb872ab2a966d329e7c1965c16851c82])]),([0x144081a2bb23a0610354764760810a68ec8ea102150dd91d240204eca588a02017652c4301083b2960c20409d8cb0510402ec6582482107632c2893b2010949445d90480a4612ec6240525101027642c248100bb2161140841d90b0614ec60425211d84082213b10084417621008c913b281094816],[(0,(0:Int),25,[0xc8082c50b54a850b17879a35a030d46028c69504639d433057d5ea8586530638d480c31182e04220422c49a388301084210b83f0f97284210850a1e1c91560280140082f0f9667673428690e2497240a8069499122aa4911348869432209882f2a419a520588080cdd2142848a1443322c48a980c63a4cd69d0985131aa3094c1a3064c163054c1230e772a084a2c9e2a1c68a161c48a0d2818694a5e352d36665566068816205480e20348030c900afddb2c4d2a3098c253428c0a341804a03a69924590d2c18b05143898c18144da625250cab0310ee332a92a78b0e7051f365c1a85715851658d0f7251961549625c05305a56a5456c5e223818d14556b82,0x13905c80e408167403a040dee07300781380142f0fe02002c1233369dc7f01480a4047658534b8d474081e1c0c01450c50a000022e8a14af86d3f8092f88934bf84a8f2a14430142c8082c8082858bfca0852dcf7ba8e44414850b342bd90e480e40b002d0f142850b142c59014dea2850b1428d1a568f31e2f86b878a34a859050d0b162858aae6073060bca81d426005a1e404142850a142851a5050b22a35e405c3d8282c50a562d0f2021b178fe1c28579303981c00b43f0e142858a1463414af34555d154d8a8ec1837ba1cd01e826005a1c2c518105a1f870a6bf0fc3])]),([0x202045328764ca04088650ec99408090c61d9328100a1843b26440040a1d8b01004030ec580402108762c08143b0109484061d8480a502042a1c3b2642061d8840a57],[(1,(0:Int),18,[0x42d00a1c5572df85af7b21c90207160458a10c50a4a267bfa816406388c05e1dd34f6da5c1d2c50af220710381402e1df74b35257c631485474081e1c00850a1b6ce87a3f2352e1e3540b0c8612c3884e8d7b21c901c8160062d0f954f4a952c54a162c6297071a1540b2031c4622bfe131d04c60ebfa5e9728650f1230ad3941c26561c50622d4b51d4870b1e1d19f2261112503091e121122812a1683b0c9922ce0b62c2a0a1242508941019224285062a2aa28689415e12065d1613c88c1c5617818916852682]),(2,(-5:Int),14,[0xa1f87e1c2f0fc3fae9cfa3e404342e2f362859d0207901c81b01e8072e060e10a16285c1d2b24ab7a5dad0e53a81e4070e0450b1428571c2a54a8e87d1935a1f070a14431002ca10b43e80acfe1ec15148302ba561520706005d010531e87d0150f43e80a2d0e162a59b43e80a87e1f6a816406388c7808a813d6411dcd8409141a7061910102839014e5c387090f382848915208471818509141c88f113c88712520324483072444a8713365d40c48390982251118683980e5838e0e30391422489cc842a1212444889872a140e7031c8a485051212dd80e400e00e])]),([0x1020661d8841363],[(0,(0:Int),33,[0xdc3b53342852ad0a90a8462afb3cb73a1502c321f6039003802c00842f69f86152e56856dfa7aa97b21c902071020f002109ee10bb0c7e9537a1d18d4dd40b2031c460bf56cc2bc881c40e0020b870a14213aa3a50a10855f4e90ad7b21c901c81600aa9285c3defa1c2bd0acc2a059018e2301055254bd04c5fe5b852a1403143ae88368b192842a080a4421a044409ca82050812144960419292a478249438a0a488850803300c04b82d0b2a0448102e48112904c40a14183100a446120a242088420a89e284840c4241c0422b22403b24a92c286e041130205210851673c48c101884c10303010c590a215d1645817818906225165c5b1640428109083d82,0x10a508414413a142cccfa1c28546ed577910808204160055454618a08af0e46a52ad42842a0980fb084d848d2bb0a97858ab90207102a038f0057494f7a1c6ab4dca9d3af2203002afe1429ce7397e97a56b146a0980bcc30d6f33492520706050e29a76579d2])]),([0x1],[(0,(0:Int),2,[0x3162852a54a18b14285a1c98102c58be02a1c2c8082c80a00416870b20290170e120040b438e9222048811222830a10244060818805210830102040b40de25093244902745c16c5a164589605715855150525485114151282])]),([0x1],[(0,(12:Int),2,[0x214a10b6024a95287870a9421cb1421e1c210e0e1628690614143023004a340dc2609524891268591625856056152545505314a525485094150a82])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r16_ok : checkRowFull 5 [15,23,27] [31] [9,9,8,8,8] 2 28 [(0,1),(2,3),(3,4)] (forbUpTo 29) (RowSpec.lemma37 (-2:Int) (-10:Int) 4 2 28) [([0x70408d035a203410d6484d00356302410d54c490034e402310d35048c034f],[(2,(-2:Int),2,[0x8a952a54a952866cb931e2c3833c2])]),([0x48c815043913215400e290814c43894215300e190c14843854315200e608414d0254310524093104148c253],[(0,(0:Int),2,[0x2005002801400a005002901480a4041a33e6cb931e2c3834c2])]),([0x28c3218b292668c2a18329266292a19328266862a08329265862988329266291a18b28265461990328a66251a10b28265251990b2826710219232a3a50209232a3a30201232a3b082211b2a39482091b2a39282011b2a3a0c21a132a3a0620a132a3a05202132a3a88221932a3906209932a3905201932a3a840a0132a3984098132a38c4088132a3a420a00b2a39420980b2a38c20900b2a3a240a1032a3924099032a3883089032a3a220a0832a3922098832a38a2090832a3a08232a1920604132a10a0504132990a06040b2a10205040b2990204820b2908207149190b2a26714899032a2670c5210b29a670c4a10329a646e],[(0,(0:Int),37,[0x4f9c9ca85421860e01148f3f6e43c81c0c1f074a97070e0f83e0f83e0e6ba4bc20b2400424aa0a50853ff47581315cd140a86e025c00a10a10a4a20d34b90c66854c6029ae67a0bd85709e116025084209a0a1085add2850c68fc1d7b018194315284d2415478a5a16c4c73306fad421860e131190c0680c11a10a0fa0ba0aa09a9d19b20607506d06504503d0353e5da200b4094075fbb6e4c3543342d51491d88c1ef1c6043046ac69c50460201500d00566bd5a9218a0568c105e85284a86284e8738dc28624a141a9461965a558cc4824848859c6241e2c18750230248228218a6124862462b6510b2a21449251451831829430c30a484192609d8b05482,0x5e1f07c1f87c1f07f01700800804ed87e5e75810435e8215dc17817002f0f83e0fc3e0f83f00800804dc170fc1db9082086ed07a09809787e1f07c1f07a1e33414cfaaedd8440871bc3040e0072becb1f9b542850c5d0568090016871890d90179f5468d90518e958986661e242d22bb4718c0408310a58b14af09])]),([0x104110c9d95328208c85d95328204c81d95324104841d95329],[(1,(0:Int),12,[0x142850a14a9740580227145ca14a14285b9082086ed07a0980142972850a95285ca68a8a142850a10adc8790380152a58a9410418aec2b84f08b002942850c50e5cb94bf421860e134261918086c28a2040c5249204184143c58718a4884480768630414412407a2d0c9112511486194111114914892898a18905198d56a74d2c59308b0a28a2420cc18c141d82]),(2,(-10:Int),18,[0x12862eb2a2f0b962b440300d2415c74b9685c08475309700587a9616ea820868e0054b67a4a62a7ee54c104520858018b4e28d47342e54a0b0ab842865a002952a54a952b30a1629548509808542619180d24114081879491050b0ea1450c0d220a09460920510609251129410c11808c08830419121430c30a214511109112092611618294498302d6c0b80f00e])]),([0x1],[(0,(0:Int),17,[0x1172e50ac82809257b002ca35a2085604160658a14ef8b01a46152180a75a876850015e729caa542642c713053bb02e03c02c079d2a54c54a942a56e410dda0f40f02c0494214210b00291925ea130c8c060340a51c51a4501042066083145126024824181269222c30a28a30922903a2520420c104828824910618a08418414c088901182])]),([0x1],[(0,(0:Int),2,[0x25085084214210c58b83e590170e94341841451020c20a2086044442444822345a1d848248a050182]),(2,(4:Int),2,[0x872842180106a48a308306288248a04107ec0b80f00e])]),([0x1],[(0,(0:Int),2,[0x3287284214210850b6020d0410318210108104110088084082081d06e42]),(2,(2:Int),2,[0x60ec0b80f00e])]),([0x1],[(0,(28:Int),2,[0x2285d0150f43e54a1432343a0d84924521942c42])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r17_ok : checkRowFull 6 [7,56] [63] [3,3,3,3,3,3] 1 12 [(0,1),(1,2),(3,4),(4,5)] (forbUpTo 30) (RowSpec.nonneg (-12:Int) 12) [([0xd1504082392a10084715421008d8a620411a94c804234a9908045c4310208b48640211650c84023310a1a84652043508c62086a1158854d022a9029a045310534089c42a8611348150c225882a18440a],[(2,(-12:Int),2,[0x952a54a952a54a952a54a952a54a9528601a00afddb766bd5a7467cd97263c587060282])]),([0x603aa310816281d4d8840b0c0e86c42058e031065432c69811b2a13b2c04d9509d8e006ca84eb2824653275540a32993a9a01194c9ce304ac864e698156432732c02b2193a30d498409c98684c204e2c332610276018832a1192e8188594c109740a40ca6284ba03106532425b01883219292c60c5880802860c4240c2856432060c2329902860d9508123121a84626143508c2c086a1151894d022930a9a0451605340898c4a8611298550c224b02a18444e],[(0,(0:Int),18,[0x1480a404b122fc28d0b3428d1b162850bc061c30e0050a142c58b162ab086cd29c2850ad3a42851a14760180142858b1629a48e9ae14614a8f80300210843ac284a70a10cdc84296aa61814116f1428556946301428531d9a286196383c0a08299e14a850a518901480a405202901480a4052029610e9578b8e2d38aca262894a233868e163854e133838a0d282cc64b511a0ba0aa09a01a00afd7a73838d0e2a3870e641950634181f40b4094074055db76660e183460b2c910a08a07a06aad84c612982609507506d06538d16521cba642c7129a26b4cbe1c9a32e2cd8f06596654e5c58d6392e6a556729a57259a595695c9364d5b1659d17155a4e95182,0xa162c58a162850b162c58a142858b162c5901480a4052025c1152fc6c50a53852af1407a0380142850a142858b162c59])]),([0xc2eca2405c8e17652102e2693b2100971345d90840b9a48ec468a5cc617603452e530bb021a973249d84d50b98a2ec06a85c185761022d490bb289014a285d94840a50a2ec06a85250c76254329424bb02299484761020884ec4021105d88402303b21a8450765340890eca86115517641202e1c63b1809172c31d8914cb8e18ec4a865ca8a7614532e3453b0aa197050dd8840b4922ec84205290c762453294453b0a29948d31d8c408b8714ec60425c2ca7632012e1a4bb189017060dd8804b4a22ec82405248a76154329164bb1908172925d8114cb8c92ec0a865c51276402129184bb1890148a25d8c840a4892ec0a865230a7630212948a3b11aa14886,0x4d23b2809172591d94408b92],[(0,(0:Int),51,[0x3f9f0ab42f2e88e06a477f0e14bf2fc28543305f85bf42b09c053fcff41b05c0f21c680b405a02d01680800d046c3869324a5c21288461621548542148e06211484307a87686686285284e84a84287285ea31cc43300ca83290c683190c4d549347281470507eb414c45191415a20a6470e1cb062a187061a18c86161cd0638d0cb1046a83060c3858c1124441ba16ae3124487246aaaa40ba0ea0fa0ca0da0aa03a4a4c1ca470a1c4873854a091824489311ca0a182805a04a00ae29123044c02281e81a80682680aaf6644a3b6e9cd2feac92b2a0d0e4732cc67cd931e2ca2e8aba25056685c94e92e6690c3919a87185366258a569915c54e705b16497c82,0xd8417bf0a53bc142850e00628ca82b537daf31c254df9b34294e178f0a5bc542b0142850af1218517e57952ad7851a17871a84fc0a1c50e04902050b6799ff7fdef060c1c60c2c0e1f8734119e542c80a415c3fae54b72a35e0912307002850850a145b4149651412557973b378731c2a1380a145a414e8b48298e5f95f16e85e3c2a19f0307183802dae1f8734114e55a70b20290170fc3f3f14a952a762858a142f0e142bc121c90e005e1f87901480a29af14285e5c699f74b7e1ca950b14285e1c2c578283941c00bc3f0e7020b1628590150fe3851a6f952fc2955a542f2ef06073038017878a1662417c7f9cf77a742bc221d10e0050851a54537d2a53,0xa1e2c5e1f870a142c50bc3f0f202901480a405c3f0fc3be68dd474cf8a538d0a34685a1ca70a346bc421e10e04b020e09d75c394ee827593c244872418b025810285e1f877653c122471218b002850a142850a342e3d2b4df6dce98e5b851b37870a342854b37871b142851b43858a84e2585b13c061c30e04f32050a1787e1dd94f04891c48a2c03c970fc3c80a4046fc50a15])]),([0xa0c3b0901703061d8840b900086b0ec584005348762c1002a1c3b16040040a1d8b01004030ec580402108762c080c3b0901482061d8840a54110ec8a65c6088765432e40443b2299490221d950ca5d],[(0,(0:Int),29,[0x13e92ad49d474a952bc122470e0254a952a526512492bc224470e014892f5af050a1c3804ca4fd474a8561ea6e88e138a1e87a1e87a1d5c4d52a57af000700380952afed52a5a1ecf6a90383012a5269257aa0d9098e230952d0e96874fd2aeeb5e010e087012a7e952d0f43a9eb51c80602549d2bd506c84c71185bd2a54ad5aa116086381c2540309494419424e15249e131444491113090a2457d1af369d5929eb9213cc47111c2473990dcbbce44d99a54881951a705847191c5279283c5870690f1253143950a21916685615124326292482])]),([0x1],[(0,(0:Int),16,[0x6de6bc1020710308144064c01cd05506c84c71180851a504295e1bc05d02e01080820408be04e020810237810388bc00a10a108449379af04081c38010846649541b2131c460285084210850a8aa0a142850a5437008704380430c0e098e1c2858a10858a94210c54b162c5e1e294f162c5e1f404391108441210884203c40f1124848211c647215c9d121442473990e0612048813948e623ae4e4a39500a4858142220e2438848a12150e12382840a10248a51926469c16858158501601c607281cc070590e4c9414092582])]),([0x1],[(0,(0:Int),2,[0x1084210862862c50b162c50866140c28246111492629864490e4290640981505214050082])]),([0x1],[(0,(12:Int),2,[0x12a54a952a54a9430921483204c0a8290a02c42])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r18_ok : checkRowFull 4 [7,11] [15] [4,4,4,4] 1 12 [(0,1),(2,3)] (forbUpTo 31) (RowSpec.nonneg (-8:Int) 8) [([0x1],[(2,(-8:Int),2,[0x3042])]),([0x30408d007426084029031420130902180940850c04b],[(0,(0:Int),2,[0x12a54a9421931e2c3832c2])]),([0x18d50804b48a8204118541030892a180844550c4022b],[(0,(0:Int),2,[0x14210a1a1e87a1f286c9194532a531e2c3834c2])]),([0x28b2a090172459504c0b862ca86205c416541202940b2a0981481950c403cd],[(0,(0:Int),5,[0x2c4e21c0084343c52dc291020e10c30e0210872a50c00834a90a4a1128a6b822e4c78b0ea603742])]),([0x210bb2a10826e085d950c41365],[(0,(0:Int),9,[0x22b4e808b550bb13887022c54430c380c383421820482b42])]),([0x1],[(0,(0:Int),2,[0x21087284342104211020492b42])]),([0x1],[(0,(0:Int),2,[0x10a10c8444949c2])]),([0x1],[(0,(0:Int),2,[0x3042])]),([0x1],[(0,(8:Int),2,[0x3042])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r19_ok : checkRowFull 6 [7,59,61] [63] [8,8,8,6,6,6] 2 27 [(1,2),(3,4),(4,5)] (forbUpTo 32) (RowSpec.nonneg (-1:Int) 1) [([0x9940843f2a89007e352100fac80421f5504803e9a10807ce30210f9a62401f2cc8403fc2a190807bc5431020e74a864021ce550c84039a2a08104725420108e2a842011b14c4082352990084695321008b88620411690c80422ca19080441a],[(2,(-1:Int),2,[0xcb972e5cb972e5cb002084383e0f83e0f83e0f83e0f838605a04a03a02a01a00afddb766bd5a7467cd97263c587060682])]),([0x660210f8ac2401f0d88403f832a10807a86532100f30c864201e91944082313290084616521008a8c8204114990804228b2108044c631020894c640211258c84023f],[(0,(0:Int),2,[0x250a10c50a50d0e972858a1cb942a5ca942854a942c00a005002c01600b005402a01500a805402a01500a8041436530d3270b0c8e59b2eaba6ef125ce8b92e2b62d4b4acab1ab8ad2b2ab2a6a729abdb766bd5a7467cd97263c587061882])]),([0x30a18543764ee1228a84ec9dc2249505d93b44862993b276888a531764ed1092a60ec9db2aa5d94c8413785122193b2a670a224317654ce0c28a64ec899c18494c5d913343062a13b1a66860a5417634cac93b2010971349d90804b8aa2ec82405c38c7630122e1a63b1881170e29d8c084b8594ec64025c3497631202e0c1bb100969449d90084a503b290807907642100f10ec64201e11d84082213b10084417621008964bb1908170615d8408b5242eca24052491764210291853b1810948c25d8c480a4512ec642052511764120290a1bb1081685a],[(0,(0:Int),45,[0x4003810f06c233068655223090905683282eb2b0c2c30a8c292834a4c03a836a43484c302814a13ac263054c131424c163038b2a2ca4aa9185891202a826a99099818549182468e192260e292858a942850b122848a11383854d133012a11a10a0fa48e091424336501a44d11282860a0c03a02a3060c1486416812a45844501a921848302281ebf4aa91a828a0146a9ca5ae8b8ae4b5b776bd9a7658984a646181236e31095606180c605184c60d2270a06231e2c9a45448c11305d0aa71b12c71314be69789871595c033428c053030c062894a23282ca05280c4892259d3232c154659361da5615e160358d72a5b14a5854074ab912806915254578189282,0x821085041234852a3d0a180e000040879bfe1c32c514ac214a54b8785292a9460214a95297ca2a50854727556e156a54c50a17d61db01d816004214a14a14210c50bc386aa3734104218a9432f38fe55b152857da1dd01e81600438384715c3c00a014ac115b62cf3343b52a5a1e2be92ec90e48b0039707cbc3adca044124d254a62d54e6687ac049eca0e50703070e5e1c6a41cb13a5245059851cd0ed0c59afa6073038014a75286533470025715f51768874458183e0fc3f0e13209ac92ad5b37b483a41c008707191052e0e49a4bbe169d12c0511488e021000013321983a85613849d2aae9461285293ebea3184a94002049c986380440084009c02200,0xa50e5cb402801000a0af8284215a862a50856f3c84214dd9a5ca14a54a67a3b00c00a14a1085801000809f8125378621084294f7494e342b8501e80e0062a50a003825e08508d1654430d1a57a952f0b346a51808439400004ac0b25a952ebc6563942a318000012704194142a50a2a271c2fb83bc03e02c0084210b002001c12b12e])]),([0x204085438764cc0408a650ec99408110ca1d9330101298c3b26502024318764ca04028610ec991848760122e0a243b08117008762100f06143b1009705061d8480b81830ec4205c10287602129080c3b0901482061d8840a5f],[(0,(0:Int),26,[0x821c04b14d74142a551f2c4e90e72a46e6f3501c13283ce0241b635288601a40aa57df4876407205801cb9700508aa1d2954b96875a15f4176087045818385293882e5c05049053768d7b083841c00a50872ab2a38e2a55b356a5420c3058065062bee538d40700da0c008210cb094e905862310020860041528a9060a550340310224029006409101a1221db75e406101490a2470a59243c60d142044333569c91204b19f7048d1214b24470904e943062a890a22432549228d2e0ba2e2b42e4ad880cb092a2484a213088c123c9090818912131e1c1a2505c59244874cd496a5615c5b1595a5542444a081484f1230855450d6444854095457818916254882,0x428421ca1780540299147285ea189cacbca15a74a75ab3905c80e408367403a0415f60770078138010858a10a54a1c01600898410830a2e58a17071a93ad4a8e8103c380ac20a3eb972e00b0d54b8d2bca8548043])]),([0x1020661d8841363],[(0,(0:Int),16,[0x10d6b0fa1e87bbc321a0a40e0c00a142a54a10a550f2020b21279d08c4c692c90b47500ad016828a01072098643f40760070058094a8102850a14295285a1c184952d0e93c78049c1c2a6efa43b203902c00a1ca14343900245b01104a05e1e2c8ab216a9504c82c71180c808535974059fc5d01680968e00c250b14210a5084e7c01072842d707c1e2d00832e7939e4461c1471213944850a0c143090814088ac01882c0a1014404901828404881019c0448111027109242248890c23a2e89a0e8520cc50812a4508064eb912e7091220448091820508122030a2c2a512103040a49106294a4ac220c2c4a102a0610a82260912202892c8b82d0a894063782,0x172040e20d4071e070fa029])]),([0x1],[(0,(0:Int),2,[0x250a1421084216005c385a1e005972a54b83e50b4020a58a1a150811203044a0818205080c4810a041340d0a41902705a16458960561525414c5254850982])]),([0x1],[(0,(1:Int),2,[0x1284210e0f83c5087878014008210d8503088c1830512689a0e81b14c324481302a4a82fc2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r20_ok : checkRowFull 6 [7,57] [63] [6,6,6,4,4,4] 2 21 [(1,2),(3,4),(4,5)] (forbUpTo 33) (RowSpec.nonneg (-18:Int) 18) [([0x13281087e551200fc6a4201f5900843eaa09007d342100f9c60421f34c4803e5990807f82105430c78a8624012e950c84025a2a08104725420108e2a842011b14c4082352990084695321008b88620411690c80422ca190804416],[(2,(-18:Int),2,[0x21084210843972e5cb972e5cb96004952e0f83e0f83e0f83e0f83e0e1b61cb871e1cd6739b66b9765b904a03a02a01a00afddb766bd5a7467cd97263c587060e82])]),([0x38c9a531644ee34b21a81778659410cbb8b2ca6805da59654302eed932a0109733c9950804b96d2ca62405cae96532102e3acb2189017268d94804b471ac62045a38b632012d69932a01094aca994c084a43301087c561200f86c4201fc19508403d432990807986432100f48ca204118994804230b290804546410208a4c840211459084022631881044a632010892c642011e29640532edd5329810972ba994c804b8f34c860425c6da6432012e4b1b2908168d2d8c840b5552ca64205271a6430212934cb2190814bceb965432104df18b182a1746a],[(0,(0:Int),34,[0xf164052020b2623a10a15a7a9d2bcb41da0e045a1e870bc3d2ecc210a15bfdb95e6a0f5070328529d8a2d1f10c6e14218b20269d2ac0da95c80a9850cd46b15bcbba8ce06a5384a9c608810881088134044408540844084409a0222042a042204d01110215d20e19a0baca6328cc96324c2d45284e83a8368328b917a696994a633968716293418a15a12a11ae6c39a899c1954653193416a10aca634cd243eb4c403adc0141540940f4035d82280a816bf04d6606ae3438b0e1c3898e162f1b29b98c994b54b64a34b0d263470d1646b19f363d54c551951c54595a7272bbce8c54706d32165716658cb139d03470d53873ce4eb9345b14e556535957255882,0x273520290551f22290950f43d0f438590148082c948a81246415d77969c341da1604e4a41520aa5df7a1e87a1e879014888a81246415bfa5de6a71507a858143d0f43d0f164052020a15e9520290d0b28aa71e7271907c8580352cbf55457642520256142c80a40536974cb120218d19e9560009058d351ac51e35e7806050f43c58a1687901480a40431a9052a49af0b17972a14285a3e2d0e372bcd21e90e0050b16870b43c80a5c5438590170e2b2a7e970a142c5a1ea85c1de590ec8703870b43d0f43d0])]),([0x1114a62ec9d612290c5d93b4424a983b2758449430764ee1448864eca99c28890c5d9533830a2993b226706125317644ce0c22a60ec8999647651022e0c2bb08116a07652100f20ec84201e21d8c8403c23b0810442762010882ec42011c28850c1d953343062a13b1a66860a5417634cd0c12a80ec6995947640122e0a1bb108169c69976432104dc70bb2908171649d90084b89a4ec84025c4d17642102e1c63b1809170d31d8c408b8714ec60425c2ca7632012e1a4bb1890170b25d8c840b8a24ec80425230a76302129184bb1890148a25d8c840a4aa2ec82405c49176421029450bb2908149551d90408b8a22ec8240529617651202e490bb28901488a,0x30a18543764ee1124a82ec9dc2145501d93b44862993b275850c432764ed],[(0,(0:Int),164,[0xa0598d204a8e50da10a11a0ea0fa0ca0aa08a09a5142eb9a8a0b39b09cf143c50601eb038909159e1c23288cb165eb9386865418188982850a0e2814c163014c06300ce722524719113450501aa34ce2715c969560d398c05a9982114843012a848a16394cd321554d70988891424489212850a112844c2154a96460615184c89c39d0c151495cf224448c121848300e80a9a5d16c591a39746032898e2a2894c2538c8245090ccd7a33e2860a0cedba7183060a0057e445110c01aac6af2e1c5851198266119c8a7070d9742a05ab8acab8d0c1c3029654266160553dc6870b112855489286ad325949a6225396222a583991430ee262258578188a649c082,0xa1697a1de4a0e50700134115d5af155a5202901580ace56b8d0b47d0e746cde1e005b46a66bc981cc0e0480a40564ab016b0b465202901580ac04f288744380000823e37e405202b015bab695212d013ca41d20e000060a7ad7a5ed7e1f87a5ca779503a81c01650a29da400082b690150fc3e80914c00020c58ffa3d12c00020db8af4470000839e35c614866228be90ac16e84e28759950f439ce86049861564a820004123251837d23182a04320432042a043204005426b0e324c5c5d08685285685aa75c951214819ae9423441bae4b07684eb95018a9545ea3554906a872a80c1ea9152818c1a2c2420aeb43a70f323c88f1a07ea14c8c91c1889338289,0x29b4bbf33caab08b7b7d5a5202901580ad9453d0e56871b16285a1f872b36414f2630303982c05ad0d1651de292141480a4056322b602d514d9ba0a3bc7f0f43d809c110e8870068414a7901480ac0564a14d68a82dde6fdd0b4794f43bca41d20e0480ad2413a004826e3bead908a7aa142a379518281d4160536dd1041428c08594146514ff4343d0f002453094001068c55cf8d1e8960525cfa238000410b2ba8d71a2fa43302fa5812158000c123213f3807c03801429b4a28a285751687b9c29a2a405202b01580b405aa22a54cf0adbf1fa2a1b2028b43c809e490e48700285a1cd841450414e8a8a2d0f6bd0e6b2901480ac05602d71150b47e8c8af0,0x5a3c28d9a368fa5c2858b478d79314181cc16005151480a87e1c28537cbf7bc614dfe8c8ecdb05480aae80ac3521268843c21c00a3121a28a901480ac3457d80ad85a0a3bc7f0f43c0091d1060480a2d8095d5a123b14cf1550590d60ef2928483a42c008c09b79614299f778514d5de1428daad78b22ae1f8f44b02c244703424a90e0d73bcd348660ff42b09c50eb3a5a11c0930c2d2828be9e680f4070029beae9ee346c515905a1e87b7c696eebc80a405602b01680b51414b7a1cc73b4fc50a1687edf405c3f0fa0247241811429ba8b71450a28b78b43d8e35b7b1cbf901480ac05602d310dadcb71a142cd915458a568f0b43d5e1de4a605072858116,0x1e2e90a424d0487243805fd0ee38b2a405202b01580b4c437d7a5c695a1e45537a72bde4a60528283943c01dd5bf7b9bf202901580ac8473d3e53851a952d1fc7f3e57bc98c0c5060730780292901480ac3457d80b53415ab74a4e08874438034974092b450ae869aed42852a19115d925223815d16e74ef2dd4f90921984bcd0ac1c0909c68082e80864400683fe2dcf747c18501c00dc6868a0828ae82852bf2ab48695901480ac05602d016a0851510b766d1f2029a778f90145b0134121c90e03ee9bf2a2b2a1d58414c7901480ac05602d1d553b34c7aa546d0f23aab346c84a404f2528283942c00b70a1a90d35edf569480a405602b19052deb7a7c68,0xfe29550d0a77d5e14295e63c5b9e405202b01580b56537970a769f69e444362d5e1de4a3050728580177d429a0aaa20a142c8882d9e682901480ac0566a3bce9da3e415162d0e146dd7930c181cc1600a8868a686752029015849b7b0168a8e98e57e84829590170f60290123a20c031e40416c05764046c2d1d16f47d1f4797e67850bc3958af2918483a42c016170f202b45051cd53e77525a0290d1547841803425490514d0531c29defbc51a17ae5fd0fcf95a1e2a438000c147000209d8e8acb9744b02e244706b8a08d048661584e15657fc500141232518a1d674000824e4c3e580ec070287b7c2f0ef39d0b202901580ac05a02d39552a7b95a7e8fe,0x182ce4271a02d01001a0b1adf0a678a08005042c57a3e0c180e04500041033deafa3b75e7549480a40562229ec05a2a3a63d0ed3e8cb40520290148096110e88700c790150f602e7e4054f8a8b42414e96f47c8082d6f56dfe1cac579494246120e90f002b7f36ef97d0593d4d5651d2b4fd6f612aa34af8bc3c52dde5450a18503a83c0165480b879f5053ff464efe80ac64d10878438028a8a3428b08d71b20233cbf8b4fd590150e90e028ee9ef3a57957be4248a60ff44b0001824e4471a02d01001a0d58d714519e57a3d0a180e005bb949f34af8010531cd71a6bd6e742eb0a9bc80a405602b01680b4e4b79d2df6d5d3e405c3e5e1d6090e48703870a,0x8872a9ae77aac95f4162c80a405602b01680b524679d2a57d1f34c7b01480b87d012c121c90e0119e19e5bd9e73c9aa405202b01580b4d463d1f36e8529e9f6bc6f3f15e4a60518283943c0e1d78444f82aa3b2029015faaef2ba022a57cd9b53e80ac3521270843c21c0004410f5de34105202901580ad746bd5ea3bc98c0c30607307801400f04ecf78d0611a485552ce85abc294f9aa8d6c8092e0e86622716118ef397e1737e3d21c2b000])]),([0x8102150e1d933010229943b26502044328764cc0404a630ec99408090c61d9330100a9843b26502014308764c8c2c3b08118060e1d8804c03050ec0425c0c28762012e08143b01094850e1d8840c02830ec2405c0c18762102e080c3b0901482061d8840a4043b1080780a],[(0,(0:Int),25,[0xa5694acb7a142e58b20aa1d2c5a1e424841860b02ba0a5b97e80e02850baaaca88602bc901c80e050e162d0f4391025969ea7e562c58b202a1c2bc821c10e068088812284214343a507150e9428580114ef4e950b2d01c050a1740517178aefb79a90586231a020a174041428c28e870cfabc710602942108421a01400a004aaae011d084390bb43952a5ca190184051130e5c1a64fdbaf225119f36514490a4454860c288a10c24e26b4ec1745c5685c96c5a54158542018805200c1579b0e6a006802bb661662205278884a531e2c39255d2442488a144908e2b2ad2b0a6292a1a128895230a948140d4818203245509115e2412248578188a4a9924c94382,0x13905c80e408367403a0415e600f02300285e1c2852204220423140a17cf39c2859a1628d0bc3c58bc3c80a6a3a040f0e00da1e872204229c1a1640520a901458bc3c80b874a9008704381202a1e8797938f21a92145f3daf8a95e42101070858070])]),([0x1],[(0,(0:Int),6,[0x70e159c82e4072041b3a01d020af300781181202901480b404440810a142858b43d0f962850ba02f0150e56290628790145a1c28ec1685615052164504091018e04111024412048a549324590e42902615454a0401649e440c040a82])]),([0x1],[(0,(0:Int),2,[0x21084210862e54b152e0e97070a1a884a0928041012498a5494a4490a4190270581585414850182])]),([0x1],[(0,(18:Int),2,[0x10852a5a1f2e5ca943602140830201483204c0a8290a02d42])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r22_ok : checkRowFull 5 [7,27] [31] [10,10,8,6,6] 2 27 [(0,1),(3,4)] (forbUpTo 34) (RowSpec.nonneg (-8:Int) 8) [([0x5900843f541200fb8c0843ed31200ff10c40823a4320108e50c84023332410072d08c401d3],[(2,(-8:Int),2,[0x254a952e0f9728421a33e6cb931e2c3834c2])]),([0x1c54310210e950c804439543210108d48403f85432100f190c14843854315200e51504082325420108c55084022c5310208a94c804239],[(0,(0:Int),2,[0x1952a5cb802c1f07a01400a005402c1c35ead3a33e6cb931e2c383642])]),([0x61b2900968a3652102d5195040843265420110c595084042c65310210a994c80442965321010c19508403c86532100f11944082226520108859484023b],[(0,(0:Int),2,[0x8421430028a10c00b07c1e00583e0e40084009c02c01450dcd1cc9c298285198932e6bd5a7467cd97263c587060482])]),([0x47651021089d948044217652101081d948403c9],[(0,(0:Int),2,[0x12a50a1429421086004170058024a943802a015008a0103524522498458414314712512412292625130542994aa353c587060582])]),([0x41061d94841363],[(0,(0:Int),20,[0x8a141b495aa54a55c110207012a6e19684c3d1a54314a560840e1c04bee2b54714285569540418014a94a10c3071189c29fa4341c181952dee10a1ca97842d52855058647b00e00e0600b00410a10842180105adc2e56614214280c06a08c58c5492061861c528682a168631229231130a3092850521922a442826086040825152ac098a0c11120921829831220a2140915c041782])]),([0x1],[(0,(0:Int),2,[0x210a10a50a5e0125a010590106944524c08608208c0420410404d160ac542ec2])]),([0x1],[(0,(0:Int),2,[0x84284210a10a5a1e878a1a0c2883043022021020822011010812128904ec2])]),([0x1],[(0,(8:Int),2,[0x854b802086c48a4320982ac2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r23_ok : checkRowFull 6 [7,59] [63] [4,4,4,2,2,2] 1 12 [(0,1),(3,4),(4,5)] (forbUpTo 35) (RowSpec.nonneg (-4:Int) 4) [([0xf150c408433281087e551200fc6a4201f5900843eaa09007d342100f9c60421f34c4803e5990807f85432100f74a864021ce550c84039a2a08104725420108e2a842011b14c4082352990084695321008b88620411690c80422ca19080441a],[(2,(-4:Int),2,[0xa142850a142850a16870a162c58b162c58b1628605a04a03a02a01a00afddb766bd5a7467cd97263c587060682])]),([0x133281088a5651201146ca42022599008444ab2090089364210111cc604222358c480445b190808b465410210e4ca840221c5950840436329881086a65320110d2ca6420217190c40842d3219008859643210108cc0421f1584803e1b10807f06542100f50ca64201e6190c8403d23288104626520108c2ca420115190408229321008451642100898c620411298c804224b190804446],[(0,(0:Int),2,[0x28421084210852a54a952a54a952a54a9707c1f07cb972e5cb972e58a1b8910a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a00afddb766bd5a7467cd97263c587061282])]),([0x61430a86ec9d19d8084442bb0900883762101148eca2042189d94804430bb2908085476410210a4ec84022145d908404263b1881084a7632011092ec64202181d948403c83b210807887632100f08ec2041109d8804220bb1080440e],[(0,(0:Int),10,[0x2850a14dd491a8f403002108428b09343a518cbdb01d80e050e1628514d050b43a3188b4385e1e2c58bc385a1e2c58bc3c5a1c2b4e1a970d1725c540ab4c8d311c687192c5a9685d29389715a57c380693768d7977e2d99b4e3db830055669932c4b2a3051682])]),([0x121d840842043b10807a04085438764c850ec40221061d884042b],[(0,(0:Int),23,[0xb0e83c1801528288285895e1ca72dc2850aac214285a1e4052020a1687a1da0b80823a8c74081e1c08a145441428529e4b414b72dc3162ac1e0c00a17870a29a0b1428dba142d0e57850a1c6b0986631564157b8d0a364052020b1504c321f6407203812020b1629a4a40416404172842e5084a70a108d0850a164052020a18b1541320b1c46028590105235c1d23269498d85548ca84489a626589c224eb962a250d22427951858512445948b9e485119030a6292a52f121a8aa98653c5a92871211306941a6485c3850e2938309cf3824496858a1305a551569595515c571a2a565238c850938a892134c8c978b0289144830a315854706309345916253a82,0x50e14285a1d5a45f9ce36872dc68da1e4052023ae04a8248122c0082e9a70a9049050a933e2d0ea2192592182182414c4e1ea4e0b83002bac82858a29a1a14a850a14685a1e4052020a1687a1d81021])]),([0x1],[(0,(0:Int),14,[0x58b1428a2a87a1c2852fd20706005151050a546a826416388c050a2ba0bd801c00e004218743d0e10e5297b203901c00842a7850a3468541320b1c460df0854a0188b15df08689673c5cf0a04856210457810515252890a10301015511124486429e22305616858150544209103020c52949551204584224041282])]),([0x1],[(0,(0:Int),2,[0x84210a142a54a10862a5086284218a1b81010204044a42906409c168591625856056154545505314a5254850582])]),([0x1],[(0,(4:Int),2,[0x84216870b142a50c204080810251204e0b02b0a82cc2])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r24_ok : checkRowFull 7 [7,120] [127] [3,3,3,2,2,2,2] 1 11 [(0,1),(1,2),(3,4),(4,5),(5,6)] (forbUpTo 36) (RowSpec.nonneg (-10:Int) 10) [([0x8a5b1908089b2a010889aaa0900899aa1080897298108896a98900895a9908088f21810888ea1890088da190808ba32a081087932a1008878b2a108087632988108753299008874b29908086e321881086d321900886cb21908085e2a1881085d2a1900885caa19080863301087e2b09007e1b10807d3281087d2a89007d1a90807cb201087caa09007c9a10807c7181087c6989007c5990807f832a10807b432990807ac321908079c2a190807b2328810471329008470b2908046a320810469321008468b21080466318810465319008464b1908045a2a08104592a1008458aa1080456298810455299008454a9908044e21881044d21900844ca1908044c2,0x333281088b2b289008b1b290808ab3201088aab209008a9b210808a73181088a6b18900],[(2,(-10:Int),2,[0x4210842108421084210842142850a142850a142850a952a54a952a54a952a54b972e5cb162c58b162c58b162c58b162c58b162862fa2ea2da2ca2ba2aa29a28a27a26a25a24a23a22a21a20a1fa1ea1da1ca1ba1aa19a18a17a16a15a14a13a12a11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a00afddb766bd5a7467cd97263c587063082])]),([0x233b01088a2bb09008a1bb10808933a8108892ba8900891ba908088b3a010888aba0900889ba1080887398108886b98900885b990808b23b288108713b29008870bb2908086a3b208108693b21008868bb210808663b188108653b19008864bb1908085a3aa08108593aa1008858baa10808563a988108553a99008854ba9908084e3a1881084d3a1900884cba19080843381087c2b89007c1b90807f03b290807a83b210807a43b190807983aa10807943a9908078c3a190807a23b08104613b1008460bb10804523a88104513a9008450ba908044a3a08104493a1008448ba1080446398810445399008444b99080448e],[(0,(0:Int),2,[0x5084210a14210bc385e1c2f0fc3c58b162c58b162c58b162d0f43d0f43d0f43d0f43d0f43d0f43d0f43d0f43d0f43f0fc3f0f602b01580ac05602b01480a405202901480a405202901480a405202c1c778e878d478d26ad25ab23a723c0e719b53c9782ec5d0b716c2b8522a21a20a1fa1ea1da1ca1ba1aa19a18a17a16a15a14a13a12a11a10a0fa0ea0da0ca0ba0aa09a08a07a06a05a04a03a02a01a00afddb766bd5a7467cd97263c587063382])]),([0x305060ca90e9dc1214329c3a7684830c870e9d60a0c2a1c3a7703050c870ea9990a0c32a439a66343b01088e2c3b09008e1c3b10808d343a81088d2c3a89008d1c3a90808cb43a01088cac3a09008c9c3a10808c743981088c6c3989008c5c3990808c3438108882c38900881c390808a243b081086143b1008860c3b108085243a881085143a9008850c3a908084a43a081084943a1008848c3a108084643988108454399008844c39908086043b108079043a908078843a10807844399080782438810441439008440c390804705090a870ec99a0c0c329c3a2646a],[(0,(0:Int),77,[0xa02b01050a142f0f43f0fc3e80b87d0158082850a1687e1f87001c14f0e16a547014aa8b8b0945692d492293e7a380bd4a5e0ad7892645f14418a5270a2dc19ac33814938f3612a0fa0ca06a09a03a00aadb9f2613a0da10a0aa04a07a01aed1af2e2c2341741d41140b5f80ab306a27c587ca0b91792578b148c578b151324949b8dd619db951b8c148d1883a94f264a1a2a164d43e493e313e1a322832626e329c8c0e8ae95931181a264d292349c98870b9d412148a94952414260a54d4b15d0b315cab464679e649e199c984d2bc158ac28ca25491a2d76e4a5c0b25592f8c25c5a530a94434a65552d2a278c854a458558be1487268cc30a9c5f1887b82,0xf7bbcafafdf0a01d40701a75410529e58d08dd614a72b19a150f41427a8371600dc829d2a63852a34a95edb8d2a9ade42496e94f43b6e943057db6b10a292c8d43c80602de852434cf35d4d3a13b5628d43d0506e1c00a15ef0a2926deb79094d496e342bd4a1837e6b6e342142d0e578549183dc28519919e35f0c01d80702504579ce34aa42dd2dca952b146a1e8284f0e005f657859a578537e42516e94f4b857a9430d784299e5ba4e857c4807901c03414569e2dd0a10a55253be2803d00e00ec83cd3f31c29de6f8d1a943000082362fccf2de2f0f14e95885abc6a48c39f6394e5ba6e8c3163aae829ae1514618c70f602d01050a16870bc3f0fc3f0f,0xa7f231c295e1469ff34df7beb70a923078a9391ce14d72a3029a53a1d8181f0e0050a14009044c7f9ae18950a6395e56a8548543c8483e1c03dca9d09af943d0503e1c00a0920a1417463fb8d7e943030a2dee95eee698eaca749183bee72aada76dca97e1518601342a22bcdf451805555e56b793d14ef8300e603806397ef7bee14297f1526394e879090bc38078a2a538a28e98e369715924a74850a92312020a7629590ba8e96f16dc2850b550ec0c1787002cd4bf72de196f14af7634bfadce958a943c8485e1c03fca7c676a95b656abae542a50f4018015a8a109d38f0ca7899e94305fdef1642454af31d246028a095fb5d5769da72a14bf4b151860,0x2434909936e16756e85a6542a1e8281f0e04f0813419b6c6ab2ae3bfe568f8c52860280120b7b68a4a6d5ba8c2958ad0a8750507c3807ea14145159452bc28a8829543c8483e1c00])]),([0x1008086439874ca0202150e61d321a61c084461661c480460e61c840460261c8403c1261c408420a61c804420661c840433],[(0,(0:Int),26,[0x5ba16698f162b8e63d1e15a0dc84d446a1330da63188bc3d8082c58b25a8bc3c58b162c5a1ea9302130250e4c09602b055829411906c426584622f0fc3f0fc3c5e1e29f023faa29e54a4488824304d33d7870d11a21816181f1d9f0708260a820447c4460622089305488a124d71e171e371e271e521e341e471e191e611e62514a9ce18b09916b9f1b9f30ae4c419594a9ac2e855d315b4953dc14d191109109f290808cb410321051107834225f034182428a49702a8545285460a179f279f3c190d29c562a8648ad4a4414434518a70c9907941642b05a8a3a609f20ca242239372e1592ac552b45552c414429847c22300c3a129648a5245492124456082,0x3d0f0e2d0e4c084c09149832c05602c3d505ca078701e746f20ae7f5f5787b01130213061306580ac0560a7c0910121c01b93ce7f8b09245910c4a628b045890c08604417c271162f0e722b091cab878b162b9f98ac84d446823509a0105328c1c88db45bfced7d0682a1c8080f0e050f438bea87b0145a1e2c58ad38df0151fc3f0febd5f097df62ab0153e981e0c0b0145e1e2f0f162f0e2f2901458b53c88a2d579e870a56acd0a36ac86b870b15511986c718c50eebb7f17c15e02ab4ff1f166dd8a4c084c184c28168f504641b1c43114e15f720af8100e20380162c58a15db5e02f0170f142f0fc3bbfe02f017808285f5caf2ddf0601cc07022c53814,0x8a1ca1e1c29702458a528816ad1f166843ae9fab17c05e02f014d9b4])]),([0x1],[(0,(0:Int),13,[0xd9c42b8847106e209c40b88071010ae7208e409c8039010763a00740412f8800f000340e1c2858a142851892d2dd0e404078700218a1628517126870a14aa41b0c4311429b08214af0af8100e20380162850b162858a692a1c28d1a906c426384640c50e142850b4385a1f87e1e870a1687edc285b010e40a80b8509088b84849103844605049e109e520503830484878447888491c78305104391210315221112109070487004c1528ac141c869b0ba1542b8590a1240cd050b3c1702829483c423c841c30a91110962291140052382])]),([0x1],[(0,(10:Int),6,[0x22c508421084295283092e201c4042be08039026004210b14210a54a95284210859a82320d8e2180a142850a94340540be109e0a1e091e088406040504049e021e011e0090a524a2930a217c0c20c8990920a40c80988a854a292522a29582a8590b417028051482])])] = true := by decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma r25_ok : checkRowFull 3 [7] [] [3,3,3] 1 9 [(0,1),(1,2)] (forbUpTo 37) (RowSpec.nonneg (-9:Int) 9) [([0x1],[(2,(-9:Int),2,[0x3042])]),([0x18c0843f4c4803ecc8403e7],[(0,(0:Int),2,[0x2850862c3831c2])]),([0x190c0844550c48044d0c8404510c4082290c8042250c84022d],[(0,(0:Int),2,[0x843162850cb931e2c383342])]),([0x1150c40842950c80442550c84042150c8403c9],[(0,(0:Int),2,[0x12a54a9431e2c383242])]),([0x1950c840483],[(0,(0:Int),2,[0x4218a1a2211103242])]),([0x1],[(0,(0:Int),2,[0x108474442221c2])]),([0x1],[(0,(0:Int),2,[0x3042])]),([0x1],[(0,(0:Int),2,[0x3042])]),([0x1],[(0,(0:Int),2,[0x3042])]),([0x1],[(0,(9:Int),2,[0x3042])])] = true := by decide +kernel

lemma hasPattern_of_three_set {F : Finset (Finset (Fin 12))}
    (hex : ∃ S ∈ F, S.card = 3) : HasPattern 3 [7] F := by
  obtain ⟨S3, hS3F, hcS3⟩ := hex
  obtain ⟨e3, he3⟩ := FranklGlobal.coordinates S3 hcS3
  refine ⟨e3, ?_⟩
  intro m hm
  simp only [List.mem_singleton] at hm
  subst hm
  rw [show (7 : ℕ) = 2 ^ 3 - 1 from rfl, decode_two_pow_sub_one, he3]
  exact hS3F

lemma solution_main : OMA.R_UnionClosed_union_closed_variants_univ_card_R2.H1 := by
  intro F closed hEmpty hUniv hex3 minSize
  by_contra hnoW
  have hforb0 : ∀ p ∈ forbUpTo 0, ¬ HasPattern p.1 p.2 F := fun _ hp => by cases hp
  have hfc1 : ¬ HasPattern 4 [11,13,14] F := fun hp => hnoW (fc_full_sound closed fc1_ok hp)
  have hforb1 : ∀ p ∈ forbUpTo 1, ¬ HasPattern p.1 p.2 F := forb_extend allPats 0 (4, [11,13,14]) rfl hforb0 hfc1
  have hfc2 : ¬ HasPattern 5 [25,26,28] F := fun hp => hnoW (fc_full_sound closed fc2_ok hp)
  have hforb2 : ∀ p ∈ forbUpTo 2, ¬ HasPattern p.1 p.2 F := forb_extend allPats 1 (5, [25,26,28]) rfl hforb1 hfc2
  have hfc3 : ¬ HasPattern 5 [21,26,28] F := fun hp => hnoW (fc_full_sound closed fc3_ok hp)
  have hforb3 : ∀ p ∈ forbUpTo 3, ¬ HasPattern p.1 p.2 F := forb_extend allPats 2 (5, [21,26,28]) rfl hforb2 hfc3
  have hfc4 : ¬ HasPattern 5 [7,26,28] F := fun hp => hnoW (fc_full_sound closed fc4_ok hp)
  have hforb4 : ∀ p ∈ forbUpTo 4, ¬ HasPattern p.1 p.2 F := forb_extend allPats 3 (5, [7,26,28]) rfl hforb3 hfc4
  have hfc5 : ¬ HasPattern 6 [7,11,52,56] F := fun hp => hnoW (fc_full_sound closed fc5_ok hp)
  have hforb5 : ∀ p ∈ forbUpTo 5, ¬ HasPattern p.1 p.2 F := forb_extend allPats 4 (6, [7,11,52,56]) rfl hforb4 hfc5
  have hfc6 : ¬ HasPattern 6 [7,25,42,52] F := fun hp => hnoW (fc_full_sound closed fc6_ok hp)
  have hforb6 : ∀ p ∈ forbUpTo 6, ¬ HasPattern p.1 p.2 F := forb_extend allPats 5 (6, [7,25,42,52]) rfl hforb5 hfc6
  have hfc7 : ¬ HasPattern 7 [81,82,100,104] F := fun hp => hnoW (fc_full_sound closed fc7_ok hp)
  have hforb7 : ∀ p ∈ forbUpTo 7, ¬ HasPattern p.1 p.2 F := forb_extend allPats 6 (7, [81,82,100,104]) rfl hforb6 hfc7
  have hfc8 : ¬ HasPattern 7 [49,82,100,104] F := fun hp => hnoW (fc_full_sound closed fc8_ok hp)
  have hforb8 : ∀ p ∈ forbUpTo 8, ¬ HasPattern p.1 p.2 F := forb_extend allPats 7 (7, [49,82,100,104]) rfl hforb7 hfc8
  have hfc9 : ¬ HasPattern 7 [25,74,100,112] F := fun hp => hnoW (fc_full_sound closed fc9_ok hp)
  have hforb9 : ∀ p ∈ forbUpTo 9, ¬ HasPattern p.1 p.2 F := forb_extend allPats 8 (7, [25,74,100,112]) rfl hforb8 hfc9
  have hfc10 : ¬ HasPattern 7 [25,88,98,100] F := fun hp => hnoW (fc_full_sound closed fc10_ok hp)
  have hforb10 : ∀ p ∈ forbUpTo 10, ¬ HasPattern p.1 p.2 F := forb_extend allPats 9 (7, [25,88,98,100]) rfl hforb9 hfc10
  have hfc11 : ¬ HasPattern 7 [13,22,104,112] F := fun hp => hnoW (fc_full_sound closed fc11_ok hp)
  have hforb11 : ∀ p ∈ forbUpTo 11, ¬ HasPattern p.1 p.2 F := forb_extend allPats 10 (7, [13,22,104,112]) rfl hforb10 hfc11
  have hfc12 : ¬ HasPattern 7 [13,28,98,112] F := fun hp => hnoW (fc_full_sound closed fc12_ok hp)
  have hforb12 : ∀ p ∈ forbUpTo 12, ¬ HasPattern p.1 p.2 F := forb_extend allPats 11 (7, [13,28,98,112]) rfl hforb11 hfc12
  have hfc13 : ¬ HasPattern 7 [56,73,82,100] F := fun hp => hnoW (fc_full_sound closed fc13_ok hp)
  have hforb13 : ∀ p ∈ forbUpTo 13, ¬ HasPattern p.1 p.2 F := forb_extend allPats 12 (7, [56,73,82,100]) rfl hforb12 hfc13
  have hfc14 : ¬ HasPattern 7 [13,50,84,104] F := fun hp => hnoW (fc_full_sound closed fc14_ok hp)
  have hforb14 : ∀ p ∈ forbUpTo 14, ¬ HasPattern p.1 p.2 F := forb_extend allPats 13 (7, [13,50,84,104]) rfl hforb13 hfc14
  have hnoFC : ∀ p ∈ fcPatterns, ¬ HasPattern p.1 p.2 F := hforb14
  have hr1 : ¬ HasPattern 5 [7,11,23] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb14 r1_ok hp)
  have hforb15 : ∀ p ∈ forbUpTo 15, ¬ HasPattern p.1 p.2 F := forb_extend allPats 14 (5, [7,11,23]) rfl hforb14 hr1
  have hr2 : ¬ HasPattern 6 [7,57,58,60] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb15 r2_ok hp)
  have hforb16 : ∀ p ∈ forbUpTo 16, ¬ HasPattern p.1 p.2 F := forb_extend allPats 15 (6, [7,57,58,60]) rfl hforb15 hr2
  have hr3 : ¬ HasPattern 6 [7,15,23,56] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb16 r3_ok hp)
  have hforb17 : ∀ p ∈ forbUpTo 17, ¬ HasPattern p.1 p.2 F := forb_extend allPats 16 (6, [7,15,23,56]) rfl hforb16 hr3
  have hr4 : ¬ HasPattern 5 [7,25] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb17 r4_ok hp)
  have hforb18 : ∀ p ∈ forbUpTo 18, ¬ HasPattern p.1 p.2 F := forb_extend allPats 17 (5, [7,25]) rfl hforb17 hr4
  have hr5 : ¬ HasPattern 6 [7,57,58] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb18 r5_ok hp)
  have hforb19 : ∀ p ∈ forbUpTo 19, ¬ HasPattern p.1 p.2 F := forb_extend allPats 18 (6, [7,57,58]) rfl hforb18 hr5
  have hr6 : ¬ HasPattern 7 [7,15,23,39,71] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb19 r6_ok hp)
  have hforb20 : ∀ p ∈ forbUpTo 20, ¬ HasPattern p.1 p.2 F := forb_extend allPats 19 (7, [7,15,23,39,71]) rfl hforb19 hr6
  have hr7 : ¬ HasPattern 6 [15,23,27,39,43,51] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb20 r7_ok hp)
  have hforb21 : ∀ p ∈ forbUpTo 21, ¬ HasPattern p.1 p.2 F := forb_extend allPats 20 (6, [15,23,27,39,43,51]) rfl hforb20 hr7
  have hr8 : ¬ HasPattern 7 [15,23,39,71] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb21 r8_ok hp)
  have hforb22 : ∀ p ∈ forbUpTo 22, ¬ HasPattern p.1 p.2 F := forb_extend allPats 21 (7, [15,23,39,71]) rfl hforb21 hr8
  have hr9 : ¬ HasPattern 6 [7,15,23,39] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb22 r9_ok hp)
  have hforb23 : ∀ p ∈ forbUpTo 23, ¬ HasPattern p.1 p.2 F := forb_extend allPats 22 (6, [7,15,23,39]) rfl hforb22 hr9
  have hr10 : ¬ HasPattern 7 [7,15,23,104] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb23 r10_ok hp)
  have hforb24 : ∀ p ∈ forbUpTo 24, ¬ HasPattern p.1 p.2 F := forb_extend allPats 23 (7, [7,15,23,104]) rfl hforb23 hr10
  have hr11 : ¬ HasPattern 6 [7,15,56] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb24 r11_ok hp)
  have hforb25 : ∀ p ∈ forbUpTo 25, ¬ HasPattern p.1 p.2 F := forb_extend allPats 24 (6, [7,15,56]) rfl hforb24 hr11
  have hr12 : ¬ HasPattern 6 [15,23,39] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb25 r12_ok hp)
  have hforb26 : ∀ p ∈ forbUpTo 26, ¬ HasPattern p.1 p.2 F := forb_extend allPats 25 (6, [15,23,39]) rfl hforb25 hr12
  have hr13 : ¬ HasPattern 5 [7,27,29] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb26 r13_ok hp)
  have hforb27 : ∀ p ∈ forbUpTo 27, ¬ HasPattern p.1 p.2 F := forb_extend allPats 26 (5, [7,27,29]) rfl hforb26 hr13
  have hr14 : ¬ HasPattern 7 [7,121,122,124] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb27 r14_ok hp)
  have hforb28 : ∀ p ∈ forbUpTo 28, ¬ HasPattern p.1 p.2 F := forb_extend allPats 27 (7, [7,121,122,124]) rfl hforb27 hr14
  have hr15 : ¬ HasPattern 6 [7,57,59] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb28 r15_ok hp)
  have hforb29 : ∀ p ∈ forbUpTo 29, ¬ HasPattern p.1 p.2 F := forb_extend allPats 28 (6, [7,57,59]) rfl hforb28 hr15
  have hr16 : ¬ HasPattern 5 [15,23,27] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb29 r16_ok hp)
  have hforb30 : ∀ p ∈ forbUpTo 30, ¬ HasPattern p.1 p.2 F := forb_extend allPats 29 (5, [15,23,27]) rfl hforb29 hr16
  have hr17 : ¬ HasPattern 6 [7,56] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb30 r17_ok hp)
  have hforb31 : ∀ p ∈ forbUpTo 31, ¬ HasPattern p.1 p.2 F := forb_extend allPats 30 (6, [7,56]) rfl hforb30 hr17
  have hr18 : ¬ HasPattern 4 [7,11] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb31 r18_ok hp)
  have hforb32 : ∀ p ∈ forbUpTo 32, ¬ HasPattern p.1 p.2 F := forb_extend allPats 31 (4, [7,11]) rfl hforb31 hr18
  have hr19 : ¬ HasPattern 6 [7,59,61] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb32 r19_ok hp)
  have hforb33 : ∀ p ∈ forbUpTo 33, ¬ HasPattern p.1 p.2 F := forb_extend allPats 32 (6, [7,59,61]) rfl hforb32 hr19
  have hr20 : ¬ HasPattern 6 [7,57] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb33 r20_ok hp)
  have hforb34 : ∀ p ∈ forbUpTo 34, ¬ HasPattern p.1 p.2 F := forb_extend allPats 33 (6, [7,57]) rfl hforb33 hr20
  have hr22 : ¬ HasPattern 5 [7,27] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb34 r22_ok hp)
  have hforb35 : ∀ p ∈ forbUpTo 35, ¬ HasPattern p.1 p.2 F := forb_extend allPats 34 (5, [7,27]) rfl hforb34 hr22
  have hr23 : ¬ HasPattern 6 [7,59] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb35 r23_ok hp)
  have hforb36 : ∀ p ∈ forbUpTo 36, ¬ HasPattern p.1 p.2 F := forb_extend allPats 35 (6, [7,59]) rfl hforb35 hr23
  have hr24 : ¬ HasPattern 7 [7,120] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb36 r24_ok hp)
  have hforb37 : ∀ p ∈ forbUpTo 37, ¬ HasPattern p.1 p.2 F := forb_extend allPats 36 (7, [7,120]) rfl hforb36 hr24
  have hr25 : ¬ HasPattern 3 [7] F := fun hp => hnoW (row_full_sound closed hEmpty hUniv minSize hnoFC hforb37 r25_ok hp)
  exact hr25 (hasPattern_of_three_set hex3)

end UCH1Sol

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_univ_card_R2.H1 := UCH1Sol.solution_main
