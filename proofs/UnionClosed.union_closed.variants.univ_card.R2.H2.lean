import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R2

/-! The minimum-four case of the twelve-element union-closed sets theorem, following the eleven four-element-compatible rows (rows 7, 8, 12, 16, 26, 27, 28, 29, 30, 31, and 32) of Vuckovic and Zivkovic (2017), Table I. -/

namespace FranklFour
open Finset UnionClosed

@[simp] theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
@[simp] theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
@[simp] theorem nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
@[simp] theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
@[simp] theorem nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

def ltNat (a n : ℕ) : Bool := !Nat.ble n a

theorem ltNat_eq (a n : ℕ) : ltNat a n = true ↔ a < n := by
  dsimp only [ltNat]
  cases h : Nat.ble n a with
  | true =>
      have hle := Nat.ble_eq.mp h
      simp only [Bool.not_true, Bool.false_eq_true, false_iff]
      omega
  | false =>
      simp only [Bool.not_false, true_iff]
      by_contra hge
      have ht : Nat.ble n a = true := Nat.ble_eq.mpr (by omega)
      rw [h] at ht; exact Bool.noConfusion ht

def unpackBytes : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, w =>
      cond (Nat.beq w 0) []
        (Nat.sub (Nat.mod w 256) 1 :: unpackBytes k (Nat.div w 256))

def unpackPerms : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, w =>
      cond (Nat.beq w 0) []
        (Nat.sub (Nat.mod w 4294967296) 1 :: unpackPerms k (Nat.div w 4294967296))

def unpackForbs : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | k + 1, w =>
      cond (Nat.beq w 0) []
        (unpackBytes 7 (Nat.mod w 18446744073709551616) ::
          unpackForbs k (Nat.div w 18446744073709551616))

def pow2 : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | 9 => 512
  | k => 1 <<< k

theorem pow2_eq (d : ℕ) : pow2 d = 1 <<< d := by
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

def decode (b m : ℕ) : Finset (Fin b) :=
  univ.filter (fun a : Fin b => m.testBit a.val)

def HasCopy (b : ℕ) (M : List ℕ) (F : Finset (Finset (Fin 12))) : Prop :=
  ∃ e : Fin b ↪ Fin 12, ∀ m ∈ M, (decode b m).map e ∈ F

def expandMasks (init : List ℕ) (pairs : List (ℕ × ℕ)) : List ℕ :=
  pairs.foldl (fun acc p => if p.1 ∈ acc ∧ p.2 ∈ acc then (p.1 ||| p.2) :: acc else acc) (0 :: init)

theorem foldl_expand_mem {b : ℕ} {F : Finset (Finset (Fin 12))} (e : Fin b ↪ Fin 12)
    (closed : IsUnionClosed F) :
    ∀ (pairs : List (ℕ × ℕ)) (acc : List ℕ),
      (∀ m ∈ acc, (decode b m).map e ∈ F) →
      ∀ m ∈ pairs.foldl (fun a p => if p.1 ∈ a ∧ p.2 ∈ a then (p.1 ||| p.2) :: a else a) acc,
        (decode b m).map e ∈ F
  | [], acc, hacc => hacc
  | p :: ps, acc, hacc => by
    dsimp only [List.foldl]
    apply foldl_expand_mem e closed ps
    split_ifs with hp
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | h
      · rw [decode, FranklLocal.decode_union, map_union]
        exact closed _ (hacc p.1 hp.1) _ (hacc p.2 hp.2)
      · exact hacc m h
    · exact hacc

theorem expandMasks_mem {b : ℕ} {F : Finset (Finset (Fin 12))} (e : Fin b ↪ Fin 12)
    (closed : IsUnionClosed F) (empty : ∅ ∈ F)
    (init : List ℕ) (hinit : ∀ m ∈ init, (decode b m).map e ∈ F)
    (pairs : List (ℕ × ℕ)) :
    ∀ m ∈ expandMasks init pairs, (decode b m).map e ∈ F := by
  apply foldl_expand_mem e closed pairs (0 :: init)
  intro m hm
  rcases List.mem_cons.mp hm with rfl | h
  · have hz : decode b 0 = ∅ := by ext a; simp [decode]
    simpa [hz] using empty
  · exact hinit m h

def bitAt : ℕ → ℕ → Bool
  | m, 0 => Nat.beq (Nat.mod m 2) 1
  | m, k + 1 => bitAt (Nat.div m 2) k

theorem bitAt_eq_testBit : ∀ m a, bitAt m a = m.testBit a
  | m, 0 => by
      simp only [bitAt, nat_mod_eq]
      rw [Nat.testBit_zero]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> decide
  | m, k + 1 => by
      simp only [bitAt, nat_div_eq]
      rw [Nat.testBit_succ]
      exact bitAt_eq_testBit (m / 2) k

theorem bitAt_eq_false_of_lt : ∀ i m, m < 2 ^ i → bitAt m i = false
  | 0, m, hm => by
      have hz : m = 0 := by omega
      subst hz; rfl
  | k + 1, m, hm => by
      simp only [bitAt, nat_div_eq]
      rw [Nat.pow_succ] at hm
      exact bitAt_eq_false_of_lt k (m / 2) (by omega)

theorem shiftLeft_succ (d : ℕ) : (1 <<< (d + 1)) = (1 <<< d) + (1 <<< d) := by
  simp [Nat.shiftLeft_eq, Nat.pow_succ]
  omega

theorem lor_comm_nat (a b : ℕ) : (a ||| b) = (b ||| a) :=
  Nat.eq_of_testBit_eq fun i => by rw [Nat.testBit_lor, Nat.testBit_lor, Bool.or_comm]

theorem lor_lt : ∀ d u g, u < 1 <<< d → g < 1 <<< d → (u ||| g) < 1 <<< d
  | 0, u, g, hu, hg => by
      have hu0 : u = 0 := by have : 1 <<< 0 = 1 := rfl; omega
      have hg0 : g = 0 := by have : 1 <<< 0 = 1 := rfl; omega
      subst hu0 hg0; decide
  | d + 1, u, g, hu, hg => by
      have hsh := shiftLeft_succ d
      have hdiv : (u ||| g) / 2 = (u / 2) ||| (g / 2) :=
        Nat.eq_of_testBit_eq fun i => by
          rw [← Nat.testBit_succ, Nat.testBit_lor, Nat.testBit_lor, Nat.testBit_succ, Nat.testBit_succ]
      have hih := lor_lt d (u / 2) (g / 2) (by omega) (by omega)
      have hdm := Nat.div_add_mod (u ||| g) 2
      omega

theorem bitAt_add_pow : ∀ d i x, x < 1 <<< d →
    bitAt (x + (1 <<< d)) i = cond (Nat.beq i d) true (bitAt x i)
  | 0, 0, x, hx => by
      have hx0 : x = 0 := by have : 1 <<< 0 = 1 := rfl; omega
      subst hx0; rfl
  | 0, k + 1, x, hx => by
      have hx0 : x = 0 := by have : 1 <<< 0 = 1 := rfl; omega
      subst hx0; rfl
  | d + 1, 0, x, _ => by
      have hsh := shiftLeft_succ d
      simp only [bitAt, nat_mod_eq]
      have hm : (x + (1 <<< (d + 1))) % 2 = x % 2 := by omega
      rw [hm]; rfl
  | d + 1, k + 1, x, hx => by
      have hsh := shiftLeft_succ d
      simp only [bitAt, nat_div_eq]
      have hd : (x + (1 <<< (d + 1))) / 2 = x / 2 + (1 <<< d) := by omega
      rw [hd, bitAt_add_pow d k (x / 2) (by omega)]
      rfl

theorem testBit_one_shift (s a : ℕ) : (1 <<< s).testBit a = Nat.beq s a := by
  have h0 : 0 < 1 <<< s := by rw [Nat.shiftLeft_eq, one_mul]; exact Nat.two_pow_pos s
  have h := bitAt_add_pow s a 0 h0
  rw [zero_add, bitAt_eq_testBit, bitAt_eq_testBit, Nat.zero_testBit] at h
  rw [h]
  by_cases hsa : s = a
  · subst hsa; simp
  · have h1 : Nat.beq a s = false := Bool.eq_false_iff.mpr (fun hh => hsa (Nat.beq_eq.mp hh).symm)
    have h2 : Nat.beq s a = false := Bool.eq_false_iff.mpr (fun hh => hsa (Nat.beq_eq.mp hh))
    rw [h1, h2]; rfl

theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α}
    (hl : l.Nodup) (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hxy)⟩
    intro hmem
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hmem
    have hay : a = y := hinj a List.mem_cons_self y (List.mem_cons_of_mem a hy) hfy.symm
    exact hl.1 (hay ▸ hy)

theorem decode_nodup (b : ℕ) : ((List.range (1 <<< b)).map (decode b)).Nodup := by
  apply nodup_map_of_inj List.nodup_range
  intro m1 hm1 m2 hm2 heq
  rw [List.mem_range, Nat.shiftLeft_eq, one_mul] at hm1 hm2
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · have hmem := Finset.ext_iff.mp heq ⟨i, hi⟩
    simp only [decode, mem_filter, mem_univ, true_and] at hmem
    exact Bool.eq_iff_iff.mpr hmem
  · have hpow : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [← bitAt_eq_testBit m1 i, ← bitAt_eq_testBit m2 i,
        bitAt_eq_false_of_lt i m1 (lt_of_lt_of_le hm1 hpow),
        bitAt_eq_false_of_lt i m2 (lt_of_lt_of_le hm2 hpow)]

theorem decode_toFinset_univ (b : ℕ) :
    ((List.range (1 <<< b)).map (decode b)).toFinset = univ := by
  apply eq_univ_of_card
  rw [List.toFinset_card_of_nodup (decode_nodup b), List.length_map, List.length_range,
      Nat.shiftLeft_eq, one_mul, Fintype.card_finset, Fintype.card_fin]

def memListNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => cond (Nat.beq x y) true (memListNat x ys)

theorem memListNat_true {x : ℕ} : ∀ {l : List ℕ}, memListNat x l = true → x ∈ l
  | [], h => by simp [memListNat] at h
  | y :: ys, h => by
      dsimp only [memListNat] at h
      by_cases hxy : x = y
      · exact hxy ▸ List.mem_cons_self
      · have hne : Nat.beq x y = false := Bool.eq_false_iff.mpr (fun hh => hxy (Nat.beq_eq.mp hh))
        rw [hne, cond_false] at h
        exact List.mem_cons_of_mem y (memListNat_true h)

def isGen (genMask g : ℕ) : Bool :=
  Nat.beq ((genMask >>> g) &&& 1) 1

def checkGenMask (n genMask : ℕ) (miExp : List ℕ) : Bool :=
  (List.range n).all fun g => !(isGen genMask g) || memListNat g miExp

theorem checkGenMask_sound {n genMask : ℕ} {miExp : List ℕ}
    (hok : checkGenMask n genMask miExp = true) :
    ∀ g < n, isGen genMask g = true → g ∈ miExp := by
  intro g hg his
  simp only [checkGenMask, List.all_eq_true, List.mem_range] at hok
  have h := hok g hg
  rw [his] at h
  simpa using memListNat_true h

theorem land_one_eq_mod (x : ℕ) : (x &&& 1) = x % 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land]
  cases i with
  | zero =>
      have h1 : (1 : ℕ).testBit 0 = true := rfl
      rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.mod_mod]
  | succ k =>
      have h1 : (1 : ℕ).testBit (k + 1) = false := by
        rw [← bitAt_eq_testBit]
        exact bitAt_eq_false_of_lt (k + 1) 1 (by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega)
      rw [h1, Bool.and_false, ← bitAt_eq_testBit,
          bitAt_eq_false_of_lt (k + 1) (x % 2) (lt_of_lt_of_le (Nat.mod_lt x (by decide)) (by
            rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega))]

theorem isGen_eq_testBit (m j : ℕ) : isGen m j = m.testBit j := by
  dsimp only [isGen]
  have ht : (m >>> j).testBit 0 = m.testBit (j + 0) := @Nat.testBit_shiftRight j 0 m
  rw [Nat.add_zero] at ht
  rw [← ht, Nat.testBit_zero, land_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> j) with h | h <;> rw [h] <;> rfl

theorem isGen_lor_shift (m bj j : ℕ) :
    isGen (m ||| (1 <<< bj)) j = (isGen m j || Nat.beq bj j) := by
  rw [isGen_eq_testBit, isGen_eq_testBit, Nat.testBit_lor, testBit_one_shift]

def maskOfList : List ℕ → ℕ
  | [] => 0
  | x :: xs => (1 <<< x) ||| maskOfList xs

theorem isGen_maskOfList_true {j : ℕ} : ∀ {l : List ℕ}, isGen (maskOfList l) j = true → j ∈ l
  | [], h => by
      have hz : isGen 0 j = false := by rw [isGen_eq_testBit, Nat.zero_testBit]
      rw [maskOfList, hz] at h; exact Bool.noConfusion h
  | x :: xs, h => by
      dsimp only [maskOfList] at h
      rw [lor_comm_nat, isGen_lor_shift, Bool.or_eq_true] at h
      rcases h with hxs | hxj
      · exact List.mem_cons_of_mem x (isGen_maskOfList_true hxs)
      · exact (Nat.beq_eq.mp hxj).symm ▸ List.mem_cons_self

def allLt (lim : ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs => ltNat x lim && allLt lim xs

theorem allLt_iff (lim : ℕ) : ∀ (l : List ℕ), allLt lim l = true ↔ ∀ x ∈ l, x < lim
  | [] => by simp [allLt]
  | x :: xs => by
      dsimp only [allLt]
      rw [Bool.and_eq_true, ltNat_eq, allLt_iff lim xs, List.forall_mem_cons]

def anyOrEq (im km : ℕ) : List ℕ → Bool
  | [] => false
  | u :: us => cond (Nat.beq im (km ||| u)) true (anyOrEq im km us)

theorem anyOrEq_true {im km : ℕ} : ∀ {l : List ℕ}, anyOrEq im km l = true → ∃ u ∈ l, im = (km ||| u)
  | [], h => by simp [anyOrEq] at h
  | u :: us, h => by
      dsimp only [anyOrEq] at h
      by_cases heq : im = (km ||| u)
      · exact ⟨u, List.mem_cons_self, heq⟩
      · have hne : Nat.beq im (km ||| u) = false :=
          Bool.eq_false_iff.mpr (fun hh => heq (Nat.beq_eq.mp hh))
        rw [hne, cond_false] at h
        obtain ⟨u', hu', heq'⟩ := anyOrEq_true h
        exact ⟨u', List.mem_cons_of_mem u hu', heq'⟩

def getNib : ℕ → ℕ → ℕ
  | p, 0 => Nat.mod p 16
  | p, k + 1 => getNib (Nat.div p 16) k

def injBelow (n bj p : ℕ) : Bool :=
  (List.range bj).all (fun i => ltNat (getNib p i) n) &&
  (List.range bj).all (fun i =>
    (List.range i).all (fun j => !Nat.beq (getNib p i) (getNib p j)))

def inImgNat (bj mj p a : ℕ) : Bool :=
  (List.range bj).any fun i => bitAt mj i && Nat.beq (getNib p i) a

def imgBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | bj + 1, mj, p =>
      let rest := imgBits bj (Nat.div mj 2) (Nat.div p 16)
      cond (Nat.beq (Nat.mod mj 2) 1) (rest ||| (1 <<< (Nat.mod p 16))) rest

theorem testBit_imgBits : ∀ bj mj p a,
    (imgBits bj mj p).testBit a = inImgNat bj mj p a
  | 0, _, _, _ => by simp [imgBits, inImgNat]
  | bj + 1, mj, p, a => by
      simp only [imgBits, inImgNat, nat_div_eq, nat_mod_eq,
        List.range_succ_eq_map, List.any_cons, List.any_map]
      dsimp only [bitAt, getNib, Function.comp_def]
      simp only [nat_div_eq, nat_mod_eq]
      have ih := testBit_imgBits bj (mj / 2) (p / 16) a
      dsimp only [inImgNat] at ih
      cases hb : Nat.beq (mj % 2) 1 with
      | false =>
          simp only [cond_false, Bool.false_and, Bool.false_or]
          exact ih
      | true =>
          simp only [cond_true, Bool.true_and, Nat.testBit_lor, ih, testBit_one_shift]
          exact Bool.or_comm _ _

def topMask (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => topMask b k ||| (1 <<< Nat.add b k)

theorem testBit_topMask (b : ℕ) : ∀ k a, a < b + k →
    (topMask b k).testBit a = Nat.ble b a
  | 0, a, ha => by
      dsimp only [topMask]
      rw [Nat.zero_testBit]
      symm; exact Bool.eq_false_iff.mpr (fun hh => by have := Nat.ble_eq.mp hh; omega)
  | k + 1, a, ha => by
      simp only [topMask, nat_add_eq]
      rw [Nat.testBit_lor, testBit_one_shift]
      by_cases heq : a = b + k
      · subst heq
        rw [Nat.beq_eq.mpr rfl, Bool.or_true, eq_comm]
        exact Nat.ble_eq.mpr (by omega)
      · have hne : Nat.beq (b + k) a = false :=
          Bool.eq_false_iff.mpr (fun hh => heq (Nat.beq_eq.mp hh).symm)
        rw [hne, Bool.or_false]
        exact testBit_topMask b k a (by omega)

def checkMj (lim genMask : ℕ) (S : List ℕ) (km im : ℕ) : Bool :=
  (ltNat im lim && isGen genMask im) || anyOrEq im km S

def checkWitnessFast (b k bj genMask : ℕ) (Mj S : List ℕ) (p : ℕ) : Bool :=
  let lim := pow2 b
  let km := topMask b k
  injBelow (Nat.add b k) bj p &&
  allLt lim S &&
  Mj.all fun mj => checkMj lim genMask S km (imgBits bj mj p)

def checkWitnessBatchList (b k bj genMask : ℕ) (Mj : List ℕ) : List (List ℕ) → List ℕ → Bool
  | [], _ => true
  | S :: rest, p :: ps =>
      checkWitnessFast b k bj genMask Mj S p &&
      checkWitnessBatchList b k bj genMask Mj rest ps
  | _ :: _, [] => false

theorem comb_embedding {b k : ℕ} (e : Fin b ↪ Fin 12) (eK : Fin k ↪ Fin 12)
    (disj : Disjoint (univ.map e) (univ.map eK)) :
    ∃ ec : Fin (b + k) ↪ Fin 12,
      (Fin.castAddEmb k).trans ec = e ∧ (Fin.natAddEmb b).trans ec = eK := by
  let fn : Fin (b + k) → Fin 12 := fun a =>
    if h : a.val < b then e ⟨a.val, h⟩ else eK ⟨a.val - b, by omega⟩
  have hinj : Function.Injective fn := by
    intro x y hxy
    dsimp [fn] at hxy
    split_ifs at hxy with hx hy hy
    · have hval : (⟨x.val, hx⟩ : Fin b) = ⟨y.val, hy⟩ := e.injective hxy
      exact Fin.ext (congrArg (Fin.val : Fin b → ℕ) hval)
    · exfalso
      exact Finset.disjoint_left.mp disj (mem_map_of_mem e (mem_univ _))
        (hxy ▸ mem_map_of_mem eK (mem_univ _))
    · exfalso
      exact Finset.disjoint_left.mp disj (hxy.symm ▸ mem_map_of_mem e (mem_univ _))
        (mem_map_of_mem eK (mem_univ _))
    · have hval : (⟨x.val - b, _⟩ : Fin k) = ⟨y.val - b, _⟩ := eK.injective hxy
      have hv : x.val - b = y.val - b := congrArg (Fin.val : Fin k → ℕ) hval
      exact Fin.ext (by omega)
  refine ⟨⟨fn, hinj⟩, ?_, ?_⟩
  · ext i
    change (fn (Fin.castAdd k i)).val = (e i).val
    dsimp [fn]
    rw [dif_pos i.isLt]
  · ext j
    change (fn (Fin.natAdd b j)).val = (eK j).val
    dsimp [fn, Fin.natAdd]
    have hnb : ¬ (b + j.val < b) := by omega
    rw [dif_neg hnb]
    congr 2
    exact Fin.ext (by dsimp; omega)

theorem testBit_false_of_lt_shift {b m a : ℕ} (hm : m < 1 <<< b) (hba : b ≤ a) :
    m.testBit a = false := by
  rw [Nat.shiftLeft_eq, one_mul] at hm
  have hpow : 2 ^ b ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) hba
  rw [← bitAt_eq_testBit]
  exact bitAt_eq_false_of_lt a m (lt_of_lt_of_le hm hpow)

theorem witness_excludes_fast {b k bj : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (sub : K ⊆ univ \ (univ.map e)) (hk : K.card = k)
    (genMask : ℕ) (hGenF : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F)
    (Mj : List ℕ) (hno : ¬ HasCopy bj Mj F)
    (S : List ℕ) (p : ℕ)
    (hw : checkWitnessFast b k bj genMask Mj S p = true) :
    ¬ (∀ u ∈ S, K ∪ (decode b u).map e ∈ F) := by
  intro hall
  simp only [checkWitnessFast, checkMj, injBelow, nat_add_eq, pow2_eq] at hw
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      List.all_eq_true, List.all_eq_true, List.all_eq_true, allLt_iff] at hw
  obtain ⟨⟨⟨hbndL, hdistL⟩, hSLt⟩, hmjAll⟩ := hw
  have hbnd : ∀ i : Fin bj, getNib p i.val < b + k := fun i =>
    (ltNat_eq _ _).mp (hbndL i.val (List.mem_range.mpr i.isLt))
  let f : Fin bj → Fin (b + k) := fun i => ⟨getNib p i.val, hbnd i⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hv : getNib p x.val = getNib p y.val := congrArg Fin.val hxy
    rcases lt_trichotomy x.val y.val with hlt | heq | hgt
    · exfalso
      have hd := hdistL y.val (List.mem_range.mpr y.isLt)
      rw [List.all_eq_true] at hd
      have hne := hd x.val (List.mem_range.mpr hlt)
      rw [hv, Nat.beq_eq.mpr rfl] at hne
      simp at hne
    · exact Fin.ext heq
    · exfalso
      have hd := hdistL x.val (List.mem_range.mpr x.isLt)
      rw [List.all_eq_true] at hd
      have hne := hd y.val (List.mem_range.mpr hgt)
      rw [hv, Nat.beq_eq.mpr rfl] at hne
      simp at hne
  have himg (mj : ℕ) (a : Fin (b + k)) :
      a ∈ (decode bj mj).image f ↔ (imgBits bj mj p).testBit a.val = true := by
    rw [testBit_imgBits]
    simp only [inImgNat, List.any_eq_true, Bool.and_eq_true, List.mem_range,
      bitAt_eq_testBit, Nat.beq_eq, mem_image, decode, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hbit, hfx⟩
      exact ⟨x.val, x.isLt, hbit, congrArg Fin.val hfx⟩
    · rintro ⟨i, hi, hbit, hp⟩
      exact ⟨⟨i, hi⟩, hbit, Fin.ext hp⟩
  obtain ⟨eK, eqK⟩ := FranklGlobal.coordinates K hk
  have disj : Disjoint (univ.map e) (univ.map eK) := by
    rw [eqK]
    exact disjoint_sdiff_self_right.mono_right sub
  obtain ⟨ec, hec1, hec2⟩ := comb_embedding e eK disj
  apply hno
  let g : Fin bj ↪ Fin (b + k) := ⟨f, hinj⟩
  refine ⟨g.trans ec, ?_⟩
  intro mj hmj
  have hmap : (decode bj mj).map (g.trans ec) = ((decode bj mj).image f).map ec := by
    rw [← map_map]
    congr 1
    ext x
    simp [g]
  rw [hmap]
  have hmj' := hmjAll mj hmj
  rw [Bool.or_eq_true] at hmj'
  rcases hmj' with h1 | h2
  · rw [Bool.and_eq_true, ltNat_eq] at h1
    have hmLt : imgBits bj mj p < 1 <<< b := h1.1
    have hmF : (decode b (imgBits bj mj p)).map e ∈ F := hGenF _ hmLt h1.2
    have hset : (decode bj mj).image f = (decode b (imgBits bj mj p)).map (Fin.castAddEmb k) := by
      ext a
      rw [himg mj a]
      by_cases hab : a.val < b
      · constructor
        · intro hbit
          exact mem_map.mpr ⟨⟨a.val, hab⟩, mem_filter.mpr ⟨mem_univ _, hbit⟩, Fin.ext rfl⟩
        · intro ha
          obtain ⟨x, hx, heqx⟩ := mem_map.mp ha
          have hval : x.val = a.val := congrArg Fin.val heqx
          simp only [decode, mem_filter, mem_univ, true_and] at hx
          exact hval ▸ hx
      · rw [testBit_false_of_lt_shift hmLt (by omega)]
        simp only [Bool.false_eq_true, false_iff]
        intro ha
        obtain ⟨x, _, heqx⟩ := mem_map.mp ha
        have hval : x.val = a.val := congrArg Fin.val heqx
        exact hab (hval ▸ x.isLt)
    rw [hset, map_map, hec1]
    exact hmF
  · obtain ⟨u, hu, him⟩ := anyOrEq_true h2
    have _ := hSLt u hu
    have hset : (decode bj mj).image f =
        (univ : Finset (Fin k)).map (Fin.natAddEmb b) ∪ (decode b u).map (Fin.castAddEmb k) := by
      ext a
      rw [himg mj a, him, Nat.testBit_lor, testBit_topMask b k a.val a.isLt, mem_union]
      by_cases hba : b ≤ a.val
      · rw [Nat.ble_eq.mpr hba, Bool.true_or]
        simp only [true_iff]
        refine Or.inl (mem_map.mpr ⟨⟨a.val - b, by omega⟩, mem_univ _, ?_⟩)
        exact Fin.ext (by change b + (a.val - b) = a.val; omega)
      · have hbl : Nat.ble b a.val = false :=
          Bool.eq_false_iff.mpr (fun hh => hba (Nat.ble_eq.mp hh))
        rw [hbl, Bool.false_or]
        have hnotK : a ∉ (univ : Finset (Fin k)).map (Fin.natAddEmb b) := by
          intro hmK
          obtain ⟨j, _, heqj⟩ := mem_map.mp hmK
          have hvj : b + j.val = a.val := congrArg Fin.val heqj
          omega
        simp only [hnotK, false_or]
        constructor
        · intro hbit
          exact mem_map.mpr ⟨⟨a.val, by omega⟩, mem_filter.mpr ⟨mem_univ _, hbit⟩, Fin.ext rfl⟩
        · intro ha
          obtain ⟨x, hx, heqx⟩ := mem_map.mp ha
          have hval : x.val = a.val := congrArg Fin.val heqx
          simp only [decode, mem_filter, mem_univ, true_and] at hx
          exact hval ▸ hx
    rw [hset, map_union, map_map, map_map, hec2, hec1, eqK]
    exact hall u hu

theorem list_indicator_le {α : Type} (P : α → Prop) [DecidablePred P] (S : List α)
    (hnot : ¬ ∀ u ∈ S, P u) :
    (S.map (fun u => if P u then (1 : ℤ) else 0)).sum ≤ (S.length : ℤ) - 1 := by
  induction S with
  | nil => exfalso; exact hnot (fun _ h => nomatch h)
  | cons a tl ih =>
    by_cases ha : P a
    · have htl : ¬ ∀ u ∈ tl, P u := fun hall => hnot fun u hu => by
        rcases List.mem_cons.mp hu with rfl | h
        · exact ha
        · exact hall u h
      have hrec := ih htl
      simp only [List.map_cons, List.sum_cons, List.length_cons, if_pos ha]
      omega
    · have hbound : (tl.map (fun u => if P u then (1 : ℤ) else 0)).sum ≤ (tl.length : ℤ) := by
        clear ih hnot ha
        induction tl with
        | nil => simp
        | cons x xs ih2 =>
          by_cases hx : P x <;>
            simp only [List.map_cons, List.sum_cons, List.length_cons, hx, ↓reduceIte] <;>
            omega
      simp only [List.map_cons, List.sum_cons, List.length_cons, if_neg ha]
      omega

theorem witness_sum_le_fast {b k bj : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (sub : K ⊆ univ \ (univ.map e)) (hk : K.card = k)
    (D : Finset (Finset (Fin b))) (hD : ∀ U, U ∈ D ↔ K ∪ U.map e ∈ F)
    (v : ℕ → ℤ) (hv : ∀ i, v i = if decode b i ∈ D then 1 else 0)
    (genMask : ℕ) (hGenF : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F)
    (Mj : List ℕ) (hno : ¬ HasCopy bj Mj F)
    (S : List ℕ) (p : ℕ)
    (hw : checkWitnessFast b k bj genMask Mj S p = true) :
    (S.map v).sum ≤ (S.length : ℤ) - 1 := by
  have hnot := witness_excludes_fast e K sub hk genMask hGenF Mj hno S p hw
  have hnotD : ¬ ∀ u ∈ S, decode b u ∈ D := fun hall =>
    hnot (fun u hu => (hD _).mp (hall u hu))
  have hle := list_indicator_le (fun u => decode b u ∈ D) S hnotD
  have hmap : S.map v = S.map (fun u => if decode b u ∈ D then (1 : ℤ) else 0) :=
    List.map_congr_left (fun u _ => hv u)
  rwa [hmap]

theorem batch_witness_list {b k bj : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (sub : K ⊆ univ \ (univ.map e)) (hk : K.card = k)
    (D : Finset (Finset (Fin b))) (hD : ∀ U, U ∈ D ↔ K ∪ U.map e ∈ F)
    (v : ℕ → ℤ) (hv : ∀ i, v i = if decode b i ∈ D then 1 else 0)
    (genMask : ℕ) (hGenF : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F)
    (Mj : List ℕ) (hno : ¬ HasCopy bj Mj F) :
    ∀ (fLists : List (List ℕ)) (pList : List ℕ),
      checkWitnessBatchList b k bj genMask Mj fLists pList = true →
      ∀ S ∈ fLists, (S.map v).sum ≤ (S.length : ℤ) - 1
  | [], _, _ => fun _ h => nomatch h
  | _ :: _, [], hw => by simp [checkWitnessBatchList] at hw
  | S :: rest, p :: ps, hw => by
      dsimp only [checkWitnessBatchList] at hw
      rw [Bool.and_eq_true] at hw
      intro X hX
      rcases List.mem_cons.mp hX with rfl | hrest
      · exact witness_sum_le_fast e K sub hk D hD v hv genMask hGenF Mj hno X p hw.1
      · exact batch_witness_list e K sub hk D hD v hv genMask hGenF Mj hno rest ps hw.2 X hrest

theorem unary_batch_list {b k bj : ℕ} {F : Finset (Finset (Fin 12))}
    (e : Fin b ↪ Fin 12) (K : Finset (Fin 12))
    (sub : K ⊆ univ \ (univ.map e)) (hk : K.card = k)
    (D : Finset (Finset (Fin b))) (hD : ∀ U, U ∈ D ↔ K ∪ U.map e ∈ F)
    (v : ℕ → ℤ) (hv : ∀ i, v i = if decode b i ∈ D then 1 else 0)
    (genMask : ℕ) (hGenF : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F)
    (Mj : List ℕ) (hno : ¬ HasCopy bj Mj F)
    (uList pList : List ℕ)
    (hw : checkWitnessBatchList b k bj genMask Mj (uList.map (fun x => [x])) pList = true) :
    ∀ u ∈ uList, v u ≤ 0 := by
  intro u hu
  have h := batch_witness_list e K sub hk D hD v hv genMask hGenF Mj hno
    (uList.map (fun x => [x])) pList hw [u] (List.mem_map.mpr ⟨u, hu, rfl⟩)
  simpa using h

theorem forbs_append {v : ℕ → ℤ} {l1 l2 : List (List ℕ)}
    (h1 : ∀ S ∈ l1, (S.map v).sum ≤ (S.length : ℤ) - 1)
    (h2 : ∀ S ∈ l2, (S.map v).sum ≤ (S.length : ℤ) - 1) :
    ∀ S ∈ l1 ++ l2, (S.map v).sum ≤ (S.length : ℤ) - 1 := by
  intro S hS
  rcases List.mem_append.mp hS with h | h
  · exact h1 S h
  · exact h2 S h

theorem zeros_append {v : ℕ → ℤ} {l1 l2 : List ℕ}
    (h1 : ∀ x ∈ l1, v x ≤ 0)
    (h2 : ∀ x ∈ l2, v x ≤ 0) :
    ∀ x ∈ l1 ++ l2, v x ≤ 0 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

theorem exclude_list {b k : ℕ} {v : ℕ → ℤ}
    (excl : ∀ i, 0 < k + (decode b i).card ∧ k + (decode b i).card < 4 → v i ≤ 0)
    (sm : List ℕ)
    (hsm : ∀ x ∈ sm, 0 < k + (decode b x).card ∧ k + (decode b x).card < 4) :
    ∀ x ∈ sm, v x ≤ 0 :=
  fun x hx => excl x (hsm x hx)

theorem stable_top {v : ℕ → ℤ} {m : ℕ} (htop : 1 ≤ v m) : ∀ x ∈ ([m] : List ℕ), 1 ≤ v x := by
  intro x hx
  rcases List.mem_singleton.mp hx with rfl
  exact htop

theorem stable_list {v : ℕ → ℤ} {m k : ℕ} {mi : List ℕ}
    (st : ∀ i, i = m ∨ (k = 0 ∧ i ∈ mi) → 1 ≤ v i)
    (ones : List ℕ)
    (hfx : ∀ x ∈ ones, x = m ∨ (k = 0 ∧ x ∈ mi)) :
    ∀ x ∈ ones, 1 ≤ v x :=
  fun x hx => st x (hfx x hx)

-- Zero-slack base-2^24 polynomial Farkas verifier

inductive FTree : Type
  | fl : ℕ → FTree
  | N : FTree → FTree → FTree

def splitEO : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: rest =>
      match splitEO rest with
      | (l1, l2) => (x :: l1, y :: l2)

theorem splitEO_mem : ∀ (l : List ℕ) (e : ℕ),
    (e ∈ (splitEO l).1 → e ∈ l) ∧ (e ∈ (splitEO l).2 → e ∈ l)
  | [], _ => ⟨id, id⟩
  | [_], _ => ⟨id, fun h => nomatch h⟩
  | x :: y :: rest, e => by
      obtain ⟨ih1, ih2⟩ := splitEO_mem rest e
      dsimp only [splitEO]
      rcases hsp : splitEO rest with ⟨l1, l2⟩
      rw [hsp] at ih1 ih2
      dsimp only at ih1 ih2 ⊢
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hr
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y (ih1 hr))
      · intro h
        rcases List.mem_cons.mp h with rfl | hr
        · exact List.mem_cons_of_mem x List.mem_cons_self
        · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y (ih2 hr))

def buildFT : ℕ → List ℕ → FTree
  | 0, [] => FTree.fl 0
  | 0, x :: _ => FTree.fl x
  | _ + 1, [] => FTree.fl 0
  | d + 1, x :: xs =>
      match splitEO (x :: xs) with
      | (l1, l2) => FTree.N (buildFT d l1) (buildFT d l2)

def lookupFT : FTree → ℕ → ℕ
  | FTree.fl e, _ => e
  | FTree.N l r, idx =>
      cond (Nat.beq (Nat.mod idx 2) 0) (lookupFT l (Nat.div idx 2)) (lookupFT r (Nat.div idx 2))

theorem lookupFT_mem : ∀ (d : ℕ) (l : List ℕ) (idx sp : ℕ),
    sp ≠ 0 → lookupFT (buildFT d l) idx = sp → sp ∈ l
  | 0, [], _, sp, hne, h => by simp [buildFT, lookupFT] at h; exact (hne h.symm).elim
  | 0, x :: _, _, _, _, h => by
      dsimp only [buildFT, lookupFT] at h
      exact h ▸ List.mem_cons_self
  | _ + 1, [], _, sp, hne, h => by simp [buildFT, lookupFT] at h; exact (hne h.symm).elim
  | d + 1, x :: xs, idx, sp, hne, h => by
      obtain ⟨ih1, ih2⟩ := splitEO_mem (x :: xs) sp
      dsimp only [buildFT] at h
      rcases hsp : splitEO (x :: xs) with ⟨l1, l2⟩
      rw [hsp] at h ih1 ih2
      dsimp only [lookupFT] at h ih1 ih2
      cases hb : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
          rw [hb, cond_true] at h
          exact ih1 (lookupFT_mem d l1 (Nat.div idx 2) sp hne h)
      | false =>
          rw [hb, cond_false] at h
          exact ih2 (lookupFT_mem d l2 (Nat.div idx 2) sp hne h)

def eqFTree : FTree → FTree → Bool
  | FTree.fl a, FTree.fl b => Nat.beq a b
  | FTree.N a0 a1, FTree.N b0 b1 => eqFTree a0 b0 && eqFTree a1 b1
  | _, _ => false

theorem eqFTree_eq : ∀ t1 t2, eqFTree t1 t2 = true → t1 = t2
  | FTree.fl a, FTree.fl b, h => congrArg FTree.fl (Nat.beq_eq.mp h)
  | FTree.N a0 a1, FTree.N b0 b1, h => by
      dsimp only [eqFTree] at h
      rw [Bool.and_eq_true] at h
      rw [eqFTree_eq a0 b0 h.1, eqFTree_eq a1 b1 h.2]
  | FTree.fl _, FTree.N _ _, h => by simp [eqFTree] at h
  | FTree.N _ _, FTree.fl _, h => by simp [eqFTree] at h

def packForbAux (n : ℕ) : List ℕ → Option ℕ
  | [] => some 0
  | u :: us =>
      cond (ltNat u n)
        (match packForbAux n us with
         | none => none
         | some r => some (Nat.add (Nat.add u 1) (Nat.mul 256 r)))
        none

def packForb (n : ℕ) (S : List ℕ) : ℕ :=
  cond (Nat.ble 1 S.length && Nat.ble S.length 7)
    (match packForbAux n S with
     | none => 0
     | some sp => sp)
    0

def addForbPack (yi : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, p, tp => (p, tp, 0)
  | k + 1, sp, p, tp =>
      cond (Nat.beq sp 0) (p, tp, 0)
        (let u := Nat.sub (Nat.mod sp 256) 1
         match addForbPack yi k (Nat.div sp 256)
             (Nat.add p (Nat.mul yi (Nat.pow 16777216 u))) (Nat.add tp yi) with
         | (p1, tp1, cnt) => (p1, tp1, Nat.add cnt 1))

inductive BaseVec : Type
  | BV : ℕ → ℕ → ℕ → ℕ → BaseVec

def buildBaseVec : ℕ → (ℕ → ℕ × ℕ) → BaseVec
  | 0, _ => BaseVec.BV 0 0 0 0
  | i + 1, cFn =>
      match buildBaseVec i cFn with
      | BaseVec.BV bp bq tp tq =>
          let c := cFn i
          BaseVec.BV
            (Nat.add bp (Nat.mul c.1 (Nat.pow 16777216 i)))
            (Nat.add bq (Nat.mul c.2 (Nat.pow 16777216 i)))
            (Nat.add tp c.1)
            (Nat.add tq c.2)

def eqBaseVec : BaseVec → BaseVec → Bool
  | BaseVec.BV a1 a2 a3 a4, BaseVec.BV b1 b2 b3 b4 =>
      (Nat.beq a1 b1 && Nat.beq a2 b2) && (Nat.beq a3 b3 && Nat.beq a4 b4)

theorem eqBaseVec_eq : ∀ q1 q2, eqBaseVec q1 q2 = true → q1 = q2
  | BaseVec.BV a1 a2 a3 a4, BaseVec.BV b1 b2 b3 b4, h => by
      dsimp only [eqBaseVec] at h
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
          Nat.beq_eq, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at h
      rw [h.1.1, h.1.2, h.2.1, h.2.2]

def pickBaseVec (n : ℕ) (cFn : ℕ → ℕ × ℕ) : Option BaseVec → BaseVec
  | some bv => bv
  | none => buildBaseVec n cFn

def okOptBaseVec (n : ℕ) (cFn : ℕ → ℕ × ℕ) : Option BaseVec → Bool
  | some bv => eqBaseVec (buildBaseVec n cFn) bv
  | none => true

theorem pickBaseVec_eq (n : ℕ) (cFn : ℕ → ℕ × ℕ) :
    ∀ obv, okOptBaseVec n cFn obv = true → pickBaseVec n cFn obv = buildBaseVec n cFn
  | none, _ => rfl
  | some _, h => (eqBaseVec_eq _ _ h).symm

inductive CTree : Type
  | C : ℕ → CTree → CTree → CTree
  | M : ℕ → ℕ → CTree
  | W : ℕ → CTree

inductive CertItem : Type
  | CI : Option BaseVec → ℕ → ℕ → FTree → CTree → CertItem

inductive OpSt : Type
  | OS : ℕ → ℕ → ℕ → ℕ → ℕ → OpSt
  | Bad : OpSt

def stepOp (n genMask : ℕ) (fTree : FTree) (op : ℕ) : OpSt → OpSt
  | OpSt.Bad => OpSt.Bad
  | OpSt.OS p q tp tq rp =>
      let knd := Nat.mod op 4
      cond (Nat.beq knd 0) (OpSt.OS p q tp tq rp)
        (cond (Nat.beq knd 1)
          (let r1 := Nat.div op 4
           let a := Nat.mod r1 128
           let r2 := Nat.div r1 128
           let c := Nat.mod r2 128
           let yi := Nat.div r2 128
           cond (ltNat a n && ltNat c n)
             (OpSt.OS
               (Nat.add (Nat.add p (Nat.mul yi (Nat.pow 16777216 a))) (Nat.mul yi (Nat.pow 16777216 c)))
               (Nat.add q (Nat.mul yi (Nat.pow 16777216 (a ||| c))))
               (Nat.add tp (Nat.mul 2 yi))
               (Nat.add tq yi)
               (Nat.add rp yi))
             OpSt.Bad)
          (cond (Nat.beq knd 2)
            (let r1 := Nat.div op 4
             let u := Nat.mod r1 128
             let r2 := Nat.div r1 128
             let g := Nat.mod r2 128
             let yi := Nat.div r2 128
             cond (ltNat u n && ltNat g n && isGen genMask g)
               (OpSt.OS
                 (Nat.add p (Nat.mul yi (Nat.pow 16777216 u)))
                 (Nat.add q (Nat.mul yi (Nat.pow 16777216 (u ||| g))))
                 (Nat.add tp yi)
                 (Nat.add tq yi)
                 rp)
               OpSt.Bad)
            (let r1 := Nat.div op 4
             let idx := Nat.mod r1 16384
             let yi := Nat.div r1 16384
             let sp := lookupFT fTree idx
             cond (Nat.beq sp 0) OpSt.Bad
               (match addForbPack yi 7 sp p tp with
                | (p1, tp1, cnt) =>
                    OpSt.OS p1 q tp1 tq (Nat.add rp (Nat.mul yi (Nat.sub cnt 1)))))))

def runOps (n genMask : ℕ) (fTree : FTree) : ℕ → ℕ → OpSt → OpSt
  | 0, _, st => st
  | k + 1, w, st =>
      cond (Nat.beq w 0) st
        (runOps n genMask fTree k (Nat.div w 268435456)
          (stepOp n genMask fTree (Nat.mod w 268435456) st))

def evalBounds : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, _, _, _, lb1, lb2 => (lb1, lb2)
  | k + 1, p, q, s0, s1, lb1, lb2 =>
      let pj := Nat.mod p 16777216
      let qj := Nat.mod q 16777216
      let lb1' := cond (Nat.ble qj pj && Nat.beq (Nat.mod s1 2) 1) (Nat.add lb1 (Nat.sub pj qj)) lb1
      let lb2' := cond (ltNat pj qj && Nat.beq (Nat.mod s0 2) 0) (Nat.add lb2 (Nat.sub qj pj)) lb2
      evalBounds k (Nat.div p 16777216) (Nat.div q 16777216) (Nat.div s0 2) (Nat.div s1 2) lb1' lb2'

def verifyLeaf (n bp bq tp tq tLbPos tLbNeg genMask : ℕ)
    (fTree : FTree) (st0 st1 m wOp : ℕ) : Bool :=
  cond (Nat.beq m 0) false
    (let p0 := cond (Nat.beq m 1) bp (Nat.mul m bp)
     let q0 := cond (Nat.beq m 1) bq (Nat.mul m bq)
     let tp0 := cond (Nat.beq m 1) tp (Nat.mul m tp)
     let tq0 := cond (Nat.beq m 1) tq (Nat.mul m tq)
     match runOps n genMask fTree 128 wOp (OpSt.OS p0 q0 tp0 tq0 0) with
     | OpSt.Bad => false
     | OpSt.OS pF qF tpF tqF dPos =>
         Nat.ble tpF 16777215 &&
         Nat.ble tqF 16777215 &&
         match evalBounds n pF qF st0 st1 0 0 with
         | (lb1, lb2) =>
             Nat.ble (Nat.add (Nat.add (Nat.add (Nat.mul m tLbPos) dPos) lb2) 1)
                     (Nat.add lb1 (Nat.mul m (Nat.add tLbNeg 1))))

def verifyCTree (n bp bq tp tq tLbPos tLbNeg genMask : ℕ)
    (fTree : FTree) : ℕ → ℕ → CTree → Bool
  | st0, st1, CTree.C bj l r =>
      ltNat bj n &&
      verifyCTree n bp bq tp tq tLbPos tLbNeg genMask fTree (st0 ||| (1 <<< bj)) st1 l &&
      verifyCTree n bp bq tp tq tLbPos tLbNeg genMask fTree st0 (st1 ||| (1 <<< bj)) r
  | st0, st1, CTree.M m wOp =>
      verifyLeaf n bp bq tp tq tLbPos tLbNeg genMask fTree st0 st1 m wOp
  | st0, st1, CTree.W wOp =>
      verifyLeaf n bp bq tp tq tLbPos tLbNeg genMask fTree st0 st1 1 wOp

def checkCertItem (n fd : ℕ) (cFn : ℕ → ℕ × ℕ) (tLbPos tLbNeg genMask : ℕ)
    (forbs : List (List ℕ)) (zeros ones : List ℕ) : CertItem → Bool
  | CertItem.CI obv st0 st1 ft ct =>
      okOptBaseVec n cFn obv &&
      Nat.beq (maskOfList zeros) st0 &&
      Nat.beq (maskOfList ones) st1 &&
      eqFTree (buildFT fd (forbs.map (packForb n))) ft &&
      match pickBaseVec n cFn obv with
      | BaseVec.BV bp bq tp tq =>
          verifyCTree n bp bq tp tq tLbPos tLbNeg genMask ft st0 st1 ct

-- Base-2^24 polynomial soundness proofs

def B24 : ℕ := 16777216

theorem nat_pow_B24 (u : ℕ) : Nat.pow 16777216 u = B24 ^ u := rfl

def polySum (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, f i * B24 ^ i

def linSum (v : ℕ → ℤ) (n : ℕ) (f : ℕ → ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (f i : ℤ) * v i

def totSum (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, f i

def updFn (f : ℕ → ℕ) (u delta i : ℕ) : ℕ :=
  if i = u then f i + delta else f i

theorem polySum_upd {n u delta : ℕ} (f : ℕ → ℕ) (hu : u < n) :
    polySum n (updFn f u delta) = polySum n f + delta * B24 ^ u := by
  simp only [polySum, updFn]
  have hmem : u ∈ Finset.range n := Finset.mem_range.mpr hu
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  simp only [↓reduceIte, add_mul]
  have heq : ∑ x ∈ (Finset.range n).erase u, (if x = u then f x + delta else f x) * B24 ^ x =
      ∑ x ∈ (Finset.range n).erase u, f x * B24 ^ x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_neg (Finset.ne_of_mem_erase hx)]
  rw [heq]; ring

theorem linSum_upd (v : ℕ → ℤ) {n u delta : ℕ} (f : ℕ → ℕ) (hu : u < n) :
    linSum v n (updFn f u delta) = linSum v n f + (delta : ℤ) * v u := by
  simp only [linSum, updFn]
  have hmem : u ∈ Finset.range n := Finset.mem_range.mpr hu
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  simp only [↓reduceIte, Nat.cast_add, add_mul]
  have heq : ∑ x ∈ (Finset.range n).erase u, ((if x = u then f x + delta else f x : ℕ) : ℤ) * v x =
      ∑ x ∈ (Finset.range n).erase u, (f x : ℤ) * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_neg (Finset.ne_of_mem_erase hx)]
  rw [heq]; ring

theorem totSum_upd {n u delta : ℕ} (f : ℕ → ℕ) (hu : u < n) :
    totSum n (updFn f u delta) = totSum n f + delta := by
  simp only [totSum, updFn]
  have hmem : u ∈ Finset.range n := Finset.mem_range.mpr hu
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem]
  simp only [↓reduceIte]
  have heq : ∑ x ∈ (Finset.range n).erase u, (if x = u then f x + delta else f x) =
      ∑ x ∈ (Finset.range n).erase u, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_neg (Finset.ne_of_mem_erase hx)]
  rw [heq]; omega

theorem le_totSum {n i : ℕ} (f : ℕ → ℕ) (hi : i < n) : f i ≤ totSum n f :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

theorem polySum_succ' (k : ℕ) (f : ℕ → ℕ) :
    polySum (k + 1) f = f 0 + B24 * polySum k (fun i => f (i + 1)) := by
  rw [polySum, Finset.sum_range_succ', pow_zero, mul_one, add_comm]
  congr 1
  rw [polySum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem linSum_succ' (v : ℕ → ℤ) (k : ℕ) (f : ℕ → ℕ) :
    linSum v (k + 1) f = (f 0 : ℤ) * v 0 + linSum (fun i => v (i + 1)) k (fun i => f (i + 1)) := by
  rw [linSum, linSum, Finset.sum_range_succ', add_comm]

theorem buildBaseVec_spec (cFn : ℕ → ℕ × ℕ) :
    ∀ n,
      buildBaseVec n cFn =
        BaseVec.BV
          (polySum n (fun i => (cFn i).1))
          (polySum n (fun i => (cFn i).2))
          (totSum n (fun i => (cFn i).1))
          (totSum n (fun i => (cFn i).2))
  | 0 => rfl
  | n + 1 => by
      dsimp only [buildBaseVec]
      rw [buildBaseVec_spec cFn n]
      simp only [polySum, totSum, Finset.sum_range_succ, nat_pow_B24, nat_mul_eq, nat_add_eq]

theorem packForbAux_spec (v : ℕ → ℤ) {n : ℕ} (hn : n ≤ 255) (yi : ℕ) :
    ∀ (S : List ℕ) (fuel sp p tp : ℕ) (f : ℕ → ℕ),
      S.length ≤ fuel →
      packForbAux n S = some sp →
      p = polySum n f → tp = totSum n f →
      ∃ f1 : ℕ → ℕ,
        addForbPack yi fuel sp p tp = (polySum n f1, totSum n f1, S.length) ∧
        linSum v n f1 = linSum v n f + (yi : ℤ) * (S.map v).sum
  | [], fuel, sp, p, tp, f, _, hpk, hp, htp => by
      simp [packForbAux] at hpk
      subst hpk
      cases fuel with
      | zero =>
          exact ⟨f, by simp [addForbPack, hp, htp], by simp⟩
      | succ k =>
          exact ⟨f, by simp [addForbPack, hp, htp], by simp⟩
  | u :: us, 0, _, _, _, _, hlen, _, _, _ => by
      simp only [List.length_cons] at hlen; omega
  | u :: us, k + 1, sp, p, tp, f, hlen, hpk, hp, htp => by
      dsimp only [packForbAux] at hpk
      cases hu : ltNat u n with
      | false => rw [hu, cond_false] at hpk; simp at hpk
      | true =>
          rw [hu, cond_true] at hpk
          rw [ltNat_eq] at hu
          cases hrec : packForbAux n us with
          | none => rw [hrec] at hpk; simp at hpk
          | some r =>
              rw [hrec] at hpk
              simp only [Option.some.injEq, nat_add_eq, nat_mul_eq] at hpk
              have hsp_pos : 0 < sp := by omega
              have hsp_ne : Nat.beq sp 0 = false :=
                Bool.eq_false_iff.mpr (fun hh => by have := Nat.beq_eq.mp hh; omega)
              have hu_eq : sp % 256 - 1 = u := by omega
              have hr_eq : sp / 256 = r := by omega
              have hp' : Nat.add p (Nat.mul yi (Nat.pow 16777216 u)) = polySum n (updFn f u yi) := by
                rw [nat_add_eq, nat_mul_eq, nat_pow_B24, hp, polySum_upd f hu]
              have htp' : Nat.add tp yi = totSum n (updFn f u yi) := by
                rw [nat_add_eq, htp, totSum_upd f hu]
              have hlen' : us.length ≤ k := by simp only [List.length_cons] at hlen; omega
              obtain ⟨f1, heq1, hlin1⟩ :=
                packForbAux_spec v hn yi us k r _ _ (updFn f u yi) hlen' hrec hp' htp'
              refine ⟨f1, ?_, ?_⟩
              · dsimp only [addForbPack]
                rw [hsp_ne, cond_false]
                simp only [nat_mod_eq, nat_sub_eq, nat_div_eq, hu_eq, hr_eq]
                rw [heq1]
                simp only [nat_add_eq, List.length_cons]
              · rw [hlin1, linSum_upd v f hu, List.map_cons, List.sum_cons]
                ring

theorem packForb_mem_spec (v : ℕ → ℤ) {n : ℕ} (hn : n ≤ 255) (yi : ℕ)
    {forbs : List (List ℕ)}
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1)
    {sp : ℕ} (hne : sp ≠ 0) (hmem : sp ∈ forbs.map (packForb n))
    {p tp : ℕ} {f : ℕ → ℕ} (hp : p = polySum n f) (htp : tp = totSum n f) :
    ∃ (f1 : ℕ → ℕ) (cnt : ℕ),
      1 ≤ cnt ∧
      addForbPack yi 7 sp p tp = (polySum n f1, totSum n f1, cnt) ∧
      linSum v n f1 ≤ linSum v n f + (yi : ℤ) * ((cnt : ℤ) - 1) := by
  obtain ⟨S, hS, heq⟩ := List.mem_map.mp hmem
  dsimp only [packForb] at heq
  cases hbnd : (Nat.ble 1 S.length && Nat.ble S.length 7) with
  | false => rw [hbnd, cond_false] at heq; exact (hne heq.symm).elim
  | true =>
      rw [hbnd, cond_true] at heq
      rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at hbnd
      cases hpk : packForbAux n S with
      | none => rw [hpk] at heq; exact (hne heq.symm).elim
      | some sp' =>
          rw [hpk] at heq
          subst heq
          obtain ⟨f1, heq1, hlin1⟩ :=
            packForbAux_spec v hn yi S 7 sp' p tp f hbnd.2 hpk hp htp
          refine ⟨f1, S.length, hbnd.1, heq1, ?_⟩
          have hmul : (yi : ℤ) * (S.map v).sum ≤ (yi : ℤ) * ((S.length : ℤ) - 1) :=
            mul_le_mul_of_nonneg_left (hforbs S hS) (Nat.cast_nonneg yi)
          linarith

def okOp (v : ℕ → ℤ) (n : ℕ) (bound : ℤ) : OpSt → Prop
  | OpSt.Bad => True
  | OpSt.OS p q tp tq rp =>
      ∃ fP fQ : ℕ → ℕ,
        p = polySum n fP ∧ q = polySum n fQ ∧
        tp = totSum n fP ∧ tq = totSum n fQ ∧
        linSum v n fP - linSum v n fQ - (rp : ℤ) ≤ bound

theorem cond_okOp {v : ℕ → ℤ} {n : ℕ} {bound : ℤ} (c : Bool) {o1 o2 : OpSt}
    (h1 : okOp v n bound o1) (h2 : okOp v n bound o2) :
    okOp v n bound (cond c o1 o2) := by
  cases c <;> assumption

theorem stepOp_ok {v : ℕ → ℤ} {b fd : ℕ} (hn : (1 <<< b) ≤ 255)
    (genMask : ℕ) (forbs : List (List ℕ))
    (join : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
    (hgens : ∀ g < (1 <<< b), isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1)
    (op : ℕ) {bound : ℤ} (st : OpSt)
    (hst : okOp v (1 <<< b) bound st) :
    okOp v (1 <<< b) bound
      (stepOp (1 <<< b) genMask (buildFT fd (forbs.map (packForb (1 <<< b)))) op st) := by
  cases st with
  | Bad => trivial
  | OS p q tp tq rp =>
      obtain ⟨fP, fQ, hp, hq, htp, htq, hle⟩ := hst
      dsimp only [stepOp]
      apply cond_okOp
      · exact ⟨fP, fQ, hp, hq, htp, htq, hle⟩
      · apply cond_okOp
        · set r1 := Nat.div op 4
          set a := Nat.mod r1 128
          set r2 := Nat.div r1 128
          set c := Nat.mod r2 128
          set yi := Nat.div r2 128
          cases hbnd : (ltNat a (1 <<< b) && ltNat c (1 <<< b)) with
          | false => trivial
          | true =>
              rw [cond_true]
              rw [Bool.and_eq_true, ltNat_eq, ltNat_eq] at hbnd
              have hac : (a ||| c) < 1 <<< b := lor_lt b a c hbnd.1 hbnd.2
              refine ⟨updFn (updFn fP a yi) c yi, updFn fQ (a ||| c) yi, ?_, ?_, ?_, ?_, ?_⟩
              · simp only [nat_add_eq, nat_mul_eq, nat_pow_B24]
                rw [polySum_upd _ hbnd.2, polySum_upd _ hbnd.1, ← hp]
              · simp only [nat_add_eq, nat_mul_eq, nat_pow_B24]
                rw [polySum_upd _ hac, ← hq]
              · rw [totSum_upd _ hbnd.2, totSum_upd _ hbnd.1, ← htp]
                simp only [nat_add_eq, nat_mul_eq]; omega
              · rw [totSum_upd _ hac, ← htq]; rfl
              · rw [linSum_upd v _ hbnd.2, linSum_upd v _ hbnd.1, linSum_upd v _ hac]
                simp only [nat_add_eq, Nat.cast_add]
                have hyi : (0 : ℤ) ≤ (yi : ℤ) := Nat.cast_nonneg _
                have hmul : (yi : ℤ) * (v a + v c - v (a ||| c)) ≤ (yi : ℤ) * 1 :=
                  mul_le_mul_of_nonneg_left (join a c) hyi
                linarith
        · apply cond_okOp
          · set r1 := Nat.div op 4
            set u := Nat.mod r1 128
            set r2 := Nat.div r1 128
            set g := Nat.mod r2 128
            set yi := Nat.div r2 128
            cases hchk : (ltNat u (1 <<< b) && ltNat g (1 <<< b) && isGen genMask g) with
            | false => trivial
            | true =>
                rw [cond_true]
                rw [Bool.and_eq_true, Bool.and_eq_true, ltNat_eq, ltNat_eq] at hchk
                obtain ⟨⟨hu, hg'⟩, hlk⟩ := hchk
                have hug : (u ||| g) < 1 <<< b := lor_lt b u g hu hg'
                refine ⟨updFn fP u yi, updFn fQ (u ||| g) yi, ?_, ?_, ?_, ?_, ?_⟩
                · simp only [nat_add_eq, nat_mul_eq, nat_pow_B24]
                  rw [polySum_upd _ hu, ← hp]
                · simp only [nat_add_eq, nat_mul_eq, nat_pow_B24]
                  rw [polySum_upd _ hug, ← hq]
                · rw [totSum_upd _ hu, ← htp]; rfl
                · rw [totSum_upd _ hug, ← htq]; rfl
                · rw [linSum_upd v _ hu, linSum_upd v _ hug]
                  have hyi : (0 : ℤ) ≤ (yi : ℤ) := Nat.cast_nonneg _
                  have hmul : (yi : ℤ) * v u ≤ (yi : ℤ) * v (u ||| g) :=
                    mul_le_mul_of_nonneg_left (hgens g hg' hlk u) hyi
                  linarith
          · set r1 := Nat.div op 4
            set idx := Nat.mod r1 16384
            set yi := Nat.div r1 16384
            set sp := lookupFT (buildFT fd (forbs.map (packForb (1 <<< b)))) idx with hsp_def
            cases hsp0 : Nat.beq sp 0 with
            | true => trivial
            | false =>
                rw [cond_false]
                have hne : sp ≠ 0 := fun hh => by rw [Nat.beq_eq.mpr hh] at hsp0; exact Bool.noConfusion hsp0
                have hmem := lookupFT_mem fd (forbs.map (packForb (1 <<< b))) idx sp hne hsp_def.symm
                obtain ⟨f1, cnt, hcnt1, hpack, hlin1⟩ :=
                  packForb_mem_spec v hn yi hforbs hne hmem hp htp
                rw [hpack]
                dsimp only
                refine ⟨f1, fQ, rfl, hq, rfl, htq, ?_⟩
                simp only [nat_add_eq, nat_mul_eq, nat_sub_eq]
                have hcast : ((rp + yi * (cnt - 1) : ℕ) : ℤ) =
                    (rp : ℤ) + (yi : ℤ) * ((cnt : ℤ) - 1) := by
                  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hcnt1]; rfl
                rw [hcast]
                linarith

theorem runOps_ok {v : ℕ → ℤ} (b fd : ℕ) (hn : (1 <<< b) ≤ 255)
    (genMask : ℕ) (forbs : List (List ℕ))
    (join : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
    (hgens : ∀ g < (1 <<< b), isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1)
    (bound : ℤ) :
    ∀ (fuel w : ℕ) (st : OpSt),
      okOp v (1 <<< b) bound st →
      okOp v (1 <<< b) bound
        (runOps (1 <<< b) genMask (buildFT fd (forbs.map (packForb (1 <<< b)))) fuel w st)
  | 0, _, _, hst => hst
  | k + 1, w, st, hst => by
      dsimp only [runOps]
      apply cond_okOp _ hst
      exact runOps_ok b fd hn genMask forbs join hgens hforbs bound k (Nat.div w 268435456) _
        (stepOp_ok hn genMask forbs join hgens hforbs (Nat.mod w 268435456) st hst)

theorem eval_coord_step (pj qj s0 s1 lb1 lb2 : ℕ) (v0 : ℤ)
    (hbit : v0 = 0 ∨ v0 = 1)
    (hs0 : s0.testBit 0 = true → v0 ≤ 0)
    (hs1 : s1.testBit 0 = true → 1 ≤ v0) :
    let lb1' := cond (Nat.ble qj pj && Nat.beq (Nat.mod s1 2) 1) (Nat.add lb1 (Nat.sub pj qj)) lb1
    let lb2' := cond (ltNat pj qj && Nat.beq (Nat.mod s0 2) 0) (Nat.add lb2 (Nat.sub qj pj)) lb2
    ((lb1' : ℤ) - (lb2' : ℤ)) - ((lb1 : ℤ) - (lb2 : ℤ)) ≤ ((pj : ℤ) - (qj : ℤ)) * v0 := by
  dsimp only
  by_cases hle : qj ≤ pj
  · have hble : Nat.ble qj pj = true := Nat.ble_eq.mpr hle
    have hlt : ltNat pj qj = false :=
      Bool.eq_false_iff.mpr (fun hh => by have := (ltNat_eq pj qj).mp hh; omega)
    simp only [hble, hlt, Bool.true_and, Bool.false_and, cond_false, nat_mod_eq, nat_add_eq, nat_sub_eq]
    rcases Nat.mod_two_eq_zero_or_one s1 with hs1_0 | hs1_1
    · rw [hs1_0, show Nat.beq 0 1 = false from rfl, cond_false]
      rcases hbit with rfl | rfl <;> omega
    · have ht1 : s1.testBit 0 = true := by rw [Nat.testBit_zero, hs1_1]; rfl
      have hv1 := hs1 ht1
      rw [hs1_1, show Nat.beq 1 1 = true from rfl, cond_true, Nat.cast_add, Nat.cast_sub hle]
      rcases hbit with rfl | rfl <;> omega
  · have hgt : pj < qj := by omega
    have hle' : pj ≤ qj := by omega
    have hble : Nat.ble qj pj = false :=
      Bool.eq_false_iff.mpr (fun hh => hle (Nat.ble_eq.mp hh))
    have hlt : ltNat pj qj = true := (ltNat_eq pj qj).mpr hgt
    simp only [hble, hlt, Bool.false_and, Bool.true_and, cond_false, nat_mod_eq, nat_add_eq, nat_sub_eq]
    rcases Nat.mod_two_eq_zero_or_one s0 with hs0_0 | hs0_1
    · rw [hs0_0, show Nat.beq 0 0 = true from rfl, cond_true, Nat.cast_add, Nat.cast_sub hle']
      rcases hbit with rfl | rfl <;> omega
    · have ht0 : s0.testBit 0 = true := by rw [Nat.testBit_zero, hs0_1]; rfl
      have hv0 := hs0 ht0
      rw [hs0_1, show Nat.beq 1 0 = false from rfl, cond_false]
      rcases hbit with rfl | rfl <;> omega

theorem evalBounds_spec :
    ∀ (k : ℕ) (v : ℕ → ℤ) (fP fQ : ℕ → ℕ) (p q s0 s1 lb1 lb2 : ℕ),
      (∀ i, v i = 0 ∨ v i = 1) →
      (∀ i < k, fP i < B24) →
      (∀ i < k, fQ i < B24) →
      p = polySum k fP →
      q = polySum k fQ →
      (∀ j < k, s0.testBit j = true → v j ≤ 0) →
      (∀ j < k, s1.testBit j = true → 1 ≤ v j) →
      (((evalBounds k p q s0 s1 lb1 lb2).1 : ℤ) - ((evalBounds k p q s0 s1 lb1 lb2).2 : ℤ)) ≤
        ((lb1 : ℤ) - (lb2 : ℤ)) + (linSum v k fP - linSum v k fQ)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp [evalBounds, linSum]
  | k + 1, v, fP, fQ, p, q, s0, s1, lb1, lb2, bit, hfP, hfQ, hp, hq, hs0, hs1 => by
      have hp_d : p = fP 0 + 16777216 * polySum k (fun i => fP (i + 1)) := by
        rw [hp, polySum_succ']; rfl
      have hq_d : q = fQ 0 + 16777216 * polySum k (fun i => fQ (i + 1)) := by
        rw [hq, polySum_succ']; rfl
      have hp0 : fP 0 < 16777216 := hfP 0 (Nat.zero_lt_succ k)
      have hq0 : fQ 0 < 16777216 := hfQ 0 (Nat.zero_lt_succ k)
      have hp_m : Nat.mod p 16777216 = fP 0 := by rw [nat_mod_eq]; omega
      have hp_v : Nat.div p 16777216 = polySum k (fun i => fP (i + 1)) := by rw [nat_div_eq]; omega
      have hq_m : Nat.mod q 16777216 = fQ 0 := by rw [nat_mod_eq]; omega
      have hq_v : Nat.div q 16777216 = polySum k (fun i => fQ (i + 1)) := by rw [nat_div_eq]; omega
      dsimp only [evalBounds]
      rw [hp_m, hq_m, hp_v, hq_v]
      set lb1' := cond (Nat.ble (fQ 0) (fP 0) && Nat.beq (Nat.mod s1 2) 1) (Nat.add lb1 (Nat.sub (fP 0) (fQ 0))) lb1
      set lb2' := cond (ltNat (fP 0) (fQ 0) && Nat.beq (Nat.mod s0 2) 0) (Nat.add lb2 (Nat.sub (fQ 0) (fP 0))) lb2
      have hstep : ((lb1' : ℤ) - (lb2' : ℤ)) - ((lb1 : ℤ) - (lb2 : ℤ)) ≤
          ((fP 0 : ℤ) - (fQ 0 : ℤ)) * v 0 :=
        eval_coord_step (fP 0) (fQ 0) s0 s1 lb1 lb2 (v 0) (bit 0)
          (hs0 0 (Nat.zero_lt_succ k)) (hs1 0 (Nat.zero_lt_succ k))
      rw [sub_mul] at hstep
      have hih := evalBounds_spec k (fun i => v (i + 1)) (fun i => fP (i + 1)) (fun i => fQ (i + 1))
        (polySum k (fun i => fP (i + 1))) (polySum k (fun i => fQ (i + 1)))
        (Nat.div s0 2) (Nat.div s1 2) lb1' lb2'
        (fun i => bit (i + 1))
        (fun i hi => hfP (i + 1) (Nat.succ_lt_succ hi))
        (fun i hi => hfQ (i + 1) (Nat.succ_lt_succ hi))
        rfl rfl
        (fun j hj ht => hs0 (j + 1) (Nat.succ_lt_succ hj) (by rw [Nat.testBit_succ, ← nat_div_eq]; exact ht))
        (fun j hj ht => hs1 (j + 1) (Nat.succ_lt_succ hj) (by rw [Nat.testBit_succ, ← nat_div_eq]; exact ht))
      rw [linSum_succ', linSum_succ']
      linarith

theorem finset_sum_range_eq_list (g : ℕ → ℤ) :
    ∀ n, (∑ i ∈ Finset.range n, g i) = ((List.range n).map g).sum
  | 0 => rfl
  | n + 1 => by
      rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append]
      simp [finset_sum_range_eq_list g n]

theorem verifyLeaf_sound {v : ℕ → ℤ} {b fd : ℕ} (hn : (1 <<< b) ≤ 255)
    (cFn : ℕ → ℕ × ℕ) (tLbPos tLbNeg genMask : ℕ) (forbs : List (List ℕ))
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
    (hgens : ∀ g < (1 <<< b), isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1)
    {st0 st1 : ℕ}
    (hst0 : ∀ j < (1 <<< b), isGen st0 j = true → v j ≤ 0)
    (hst1 : ∀ j < (1 <<< b), isGen st1 j = true → 1 ≤ v j)
    (m wOp : ℕ)
    (hok : verifyLeaf (1 <<< b)
      (polySum (1 <<< b) (fun i => (cFn i).1))
      (polySum (1 <<< b) (fun i => (cFn i).2))
      (totSum (1 <<< b) (fun i => (cFn i).1))
      (totSum (1 <<< b) (fun i => (cFn i).2))
      tLbPos tLbNeg genMask (buildFT fd (forbs.map (packForb (1 <<< b))))
      st0 st1 m wOp = true) :
    (tLbPos : ℤ) - (tLbNeg : ℤ) ≤
      ((List.range (1 <<< b)).map (fun i => (((cFn i).1 : ℤ) - ((cFn i).2 : ℤ)) * v i)).sum := by
  by_contra! hbad
  set n := 1 <<< b
  have hbad1 : ((List.range n).map (fun i =>
      (((cFn i).1 : ℤ) - ((cFn i).2 : ℤ)) * v i)).sum ≤
    (tLbPos : ℤ) - (tLbNeg : ℤ) - 1 := Int.le_sub_one_of_lt hbad
  have hlinBase : linSum v n (fun i => (cFn i).1) - linSum v n (fun i => (cFn i).2) =
      ((List.range n).map (fun i => (((cFn i).1 : ℤ) - ((cFn i).2 : ℤ)) * v i)).sum := by
    rw [← finset_sum_range_eq_list, linSum, linSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only [verifyLeaf] at hok
  by_cases hm0 : m = 0
  · rw [Nat.beq_eq.mpr hm0, cond_true] at hok; simp at hok
  · have hnm0 : Nat.beq m 0 = false := Bool.eq_false_iff.mpr (fun hh => hm0 (Nat.beq_eq.mp hh))
    rw [hnm0, cond_false] at hok
    have hmulVal (x : ℕ) : cond (Nat.beq m 1) x (Nat.mul m x) = m * x := by
      by_cases hm1 : m = 1
      · subst hm1; simp
      · have hne : Nat.beq m 1 = false := Bool.eq_false_iff.mpr (fun hh => hm1 (Nat.beq_eq.mp hh))
        rw [hne, cond_false, nat_mul_eq]
    rw [hmulVal, hmulVal, hmulVal, hmulVal] at hok
    let initP : ℕ → ℕ := fun i => m * (cFn i).1
    let initQ : ℕ → ℕ := fun i => m * (cFn i).2
    have hp0 : m * polySum n (fun i => (cFn i).1) = polySum n initP := by
      simp only [polySum, initP, Finset.mul_sum, mul_assoc]
    have hq0 : m * polySum n (fun i => (cFn i).2) = polySum n initQ := by
      simp only [polySum, initQ, Finset.mul_sum, mul_assoc]
    have htp0 : m * totSum n (fun i => (cFn i).1) = totSum n initP := by
      simp only [totSum, initP, Finset.mul_sum]
    have htq0 : m * totSum n (fun i => (cFn i).2) = totSum n initQ := by
      simp only [totSum, initQ, Finset.mul_sum]
    have hlin0 : linSum v n initP - linSum v n initQ ≤ (m : ℤ) * ((tLbPos : ℤ) - (tLbNeg : ℤ) - 1) := by
      have heqL : linSum v n initP - linSum v n initQ =
          (m : ℤ) * (linSum v n (fun i => (cFn i).1) - linSum v n (fun i => (cFn i).2)) := by
        simp only [linSum, initP, initQ, Nat.cast_mul, mul_assoc, ← Finset.mul_sum, mul_sub]
      rw [heqL, hlinBase]
      exact mul_le_mul_of_nonneg_left hbad1 (Nat.cast_nonneg m)
    have hInitOk : okOp v n (linSum v n initP - linSum v n initQ)
        (OpSt.OS (m * polySum n (fun i => (cFn i).1)) (m * polySum n (fun i => (cFn i).2))
          (m * totSum n (fun i => (cFn i).1)) (m * totSum n (fun i => (cFn i).2)) 0) :=
      ⟨initP, initQ, hp0, hq0, htp0, htq0, by simp⟩
    have hRunOp := runOps_ok b fd hn genMask forbs join hgens hforbs
      (linSum v n initP - linSum v n initQ) 128 wOp _ hInitOk
    cases hro : runOps n genMask (buildFT fd (forbs.map (packForb n))) 128 wOp
        (OpSt.OS (m * polySum n (fun i => (cFn i).1)) (m * polySum n (fun i => (cFn i).2))
          (m * totSum n (fun i => (cFn i).1)) (m * totSum n (fun i => (cFn i).2)) 0) with
    | Bad => rw [hro] at hok; simp at hok
    | OS pF qF tpF tqF dPos =>
        rw [hro] at hok hRunOp
        dsimp only at hok
        obtain ⟨fP, fQ, epF, eqF, etpF, etqF, evOp⟩ := hRunOp
        rcases heb : evalBounds n pF qF st0 st1 0 0 with ⟨lb1, lb2⟩
        rw [heb] at hok
        dsimp only at hok
        simp only [Bool.and_eq_true, Nat.ble_eq, nat_add_eq, nat_mul_eq] at hok
        obtain ⟨⟨hbnd1, hbnd2⟩, hfinalLe⟩ := hok
        have hfP_lt : ∀ i < n, fP i < B24 := fun i hi => by
          have := le_totSum fP hi; rw [← etpF] at this; dsimp only [B24]; omega
        have hfQ_lt : ∀ i < n, fQ i < B24 := fun i hi => by
          have := le_totSum fQ hi; rw [← etqF] at this; dsimp only [B24]; omega
        have hspec := evalBounds_spec n v fP fQ pF qF st0 st1 0 0 bit hfP_lt hfQ_lt epF eqF
          (fun j hj ht => hst0 j hj (by rw [isGen_eq_testBit]; exact ht))
          (fun j hj ht => hst1 j hj (by rw [isGen_eq_testBit]; exact ht))
        rw [heb] at hspec
        simp only [Nat.cast_zero, sub_zero, zero_add] at hspec
        have hfinalZ : ((m * tLbPos + dPos + lb2 + 1 : ℕ) : ℤ) ≤
            ((lb1 + m * (tLbNeg + 1) : ℕ) : ℤ) := Nat.cast_le.mpr hfinalLe
        push_cast at hfinalZ
        linarith

theorem verifyCTree_sound {v : ℕ → ℤ} {b fd : ℕ} (hn : (1 <<< b) ≤ 255)
    (cFn : ℕ → ℕ × ℕ) (tLbPos tLbNeg genMask : ℕ) (forbs : List (List ℕ))
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
    (hgens : ∀ g < (1 <<< b), isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1) :
    ∀ (ct : CTree) (st0 st1 : ℕ),
      (∀ j < (1 <<< b), isGen st0 j = true → v j ≤ 0) →
      (∀ j < (1 <<< b), isGen st1 j = true → 1 ≤ v j) →
      verifyCTree (1 <<< b)
        (polySum (1 <<< b) (fun i => (cFn i).1))
        (polySum (1 <<< b) (fun i => (cFn i).2))
        (totSum (1 <<< b) (fun i => (cFn i).1))
        (totSum (1 <<< b) (fun i => (cFn i).2))
        tLbPos tLbNeg genMask (buildFT fd (forbs.map (packForb (1 <<< b))))
        st0 st1 ct = true →
      (tLbPos : ℤ) - (tLbNeg : ℤ) ≤
        ((List.range (1 <<< b)).map (fun i => (((cFn i).1 : ℤ) - ((cFn i).2 : ℤ)) * v i)).sum
  | CTree.C bj l r, st0, st1, hst0, hst1, hok => by
      dsimp only [verifyCTree] at hok
      rw [Bool.and_eq_true, Bool.and_eq_true, ltNat_eq] at hok
      obtain ⟨⟨hbj, hL⟩, hR⟩ := hok
      rcases bit bj with h0 | h1
      · apply verifyCTree_sound hn cFn tLbPos tLbNeg genMask forbs bit join hgens hforbs l _ _ _ hst1 hL
        intro j hj his
        rw [isGen_lor_shift, Bool.or_eq_true] at his
        rcases his with hs | heq
        · exact hst0 j hj hs
        · rw [← Nat.beq_eq.mp heq, h0]
      · apply verifyCTree_sound hn cFn tLbPos tLbNeg genMask forbs bit join hgens hforbs r _ _ hst0 _ hR
        intro j hj his
        rw [isGen_lor_shift, Bool.or_eq_true] at his
        rcases his with hs | heq
        · exact hst1 j hj hs
        · rw [← Nat.beq_eq.mp heq, h1]
  | CTree.M m wOp, st0, st1, hst0, hst1, hok =>
      verifyLeaf_sound hn cFn tLbPos tLbNeg genMask forbs bit join hgens hforbs hst0 hst1 m wOp hok
  | CTree.W wOp, st0, st1, hst0, hst1, hok =>
      verifyLeaf_sound hn cFn tLbPos tLbNeg genMask forbs bit join hgens hforbs hst0 hst1 1 wOp hok

theorem cert_step {v : ℕ → ℤ} (b fd : ℕ) (hn : (1 <<< b) ≤ 255) (cFn : ℕ → ℕ × ℕ)
    (tLbPos tLbNeg genMask : ℕ)
    (forbs : List (List ℕ)) (zeros ones : List ℕ) {ci : CertItem}
    (bit : ∀ i, v i = 0 ∨ v i = 1)
    (join : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
    (hgens : ∀ g < (1 <<< b), isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
    (hforbs : ∀ S ∈ forbs, (S.map v).sum ≤ (S.length : ℤ) - 1)
    (hz : ∀ x ∈ zeros, v x ≤ 0)
    (ho : ∀ x ∈ ones, 1 ≤ v x)
    (hchk : checkCertItem (pow2 b) fd cFn tLbPos tLbNeg genMask forbs zeros ones ci = true) :
    (tLbPos : ℤ) - (tLbNeg : ℤ) ≤
      ((List.range (1 <<< b)).map (fun i => (((cFn i).1 : ℤ) - ((cFn i).2 : ℤ)) * v i)).sum := by
  rcases ci with ⟨obv, st0, st1, ft, ct⟩
  simp only [checkCertItem, pow2_eq] at hchk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hBase, hSt0⟩, hSt1⟩, hFt⟩, hok⟩ := hchk
  rw [pickBaseVec_eq _ _ obv hBase, buildBaseVec_spec] at hok
  dsimp only at hok
  rw [← Nat.beq_eq.mp hSt0, ← Nat.beq_eq.mp hSt1, ← eqFTree_eq _ _ hFt] at hok
  exact verifyCTree_sound hn cFn tLbPos tLbNeg genMask forbs bit join hgens hforbs
    ct _ _
    (fun j _ his => hz j (isGen_maskOfList_true his))
    (fun j _ his => ho j (isGen_maskOfList_true his))
    hok

-- Multi-weight slice and global reassembly infrastructure

theorem multi_slice_data {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12)
    (K : Finset (Fin 12))
    (closed : IsUnionClosed F) (empty : ∅ ∈ F) (fullSet : univ ∈ F)
    (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hK : K ⊆ univ \ (univ.map e)) :
    let B := univ.map e
    let X (U : Finset (Fin b)) := K ∪ U.map e
    let D := univ.filter fun U => X U ∈ F
    IsUnionClosed D ∧ (K = ∅ → ∅ ∈ D) ∧ (K = univ \ B → univ ∈ D) ∧
    (∀ U ∈ D, K.card + U.card = 0 ∨ 4 ≤ K.card + U.card) ∧
    (∀ H : Finset (Fin b), H.map e ∈ F → ∀ U ∈ D, U ∪ H ∈ D) ∧
    (∀ g : Finset (Fin b) → ℤ,
      (∑ Y ∈ F.filter (fun Y => Y \ B = K), g (univ.filter (fun j => e j ∈ Y))) =
        ∑ U ∈ D, g U) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  let X (U : Finset (Fin b)) := K ∪ U.map e
  let D := (univ : Finset (Finset (Fin b))).filter fun U => X U ∈ F
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
  change IsUnionClosed D ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hu V hv
    apply (mem _).mpr
    have := closed (X U) ((mem U).mp hu) (X V) ((mem V).mp hv)
    simpa [X, map_union, union_assoc, union_left_comm, union_comm] using this
  · intro z; apply (mem _).mpr; simpa [X, z] using empty
  · intro z; apply (mem _).mpr
    have eq : X univ = univ := by ext i; simp [X, z]
    rwa [eq]
  · intro U hu
    by_cases h : (X U).Nonempty
    · exact Or.inr ((cardX U) ▸ minSize _ ((mem _).mp hu) h)
    · have z : X U = ∅ := not_nonempty_iff_eq_empty.mp h
      exact Or.inl (by simpa [z] using (cardX U).symm)
  · intro H hH U hu
    apply (mem _).mpr
    have := closed _ ((mem _).mp hu) _ hH
    simpa [X, map_union, union_assoc] using this
  · intro g
    have eq : D.image X = F.filter (fun Y => Y \ B = K) := by
      ext Y
      constructor
      · rintro hy
        obtain ⟨U, hu, rfl⟩ := mem_image.mp hy
        exact mem_filter.mpr ⟨(mem _).mp hu, out U⟩
      · intro hy
        obtain ⟨hf, base⟩ := mem_filter.mp hy
        let U := univ.filter (fun i : Fin b => e i ∈ Y)
        have val : X U = Y := by
          ext a
          simp only [X, mem_union]
          by_cases h : a ∈ B
          · obtain ⟨i, _, rfl⟩ := mem_map.mp h
            have nk : e i ∉ K := fun hm =>
              disjoint_left.mp dis hm (inner univ (mem_map.mpr ⟨i, mem_univ _, rfl⟩))
            simp [U, nk]
          · have : a ∈ K ↔ a ∈ Y := by rw [← base]; simp [h]
            have hn : a ∉ U.map e := fun hu => h (inner U hu)
            simp [hn, this]
        exact mem_image.mpr ⟨U, (mem _).mpr (val ▸ hf), val⟩
    rw [← eq, sum_image (fun _ _ _ _ eq => inject eq)]
    apply sum_congr rfl
    intro U _
    congr 1
    ext j
    have nk : e j ∉ K := fun hm =>
      disjoint_left.mp dis hm (inner univ (mem_map.mpr ⟨j, mem_univ _, rfl⟩))
    simp [X, nk]

theorem multi_weight_witness {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12)
    (w_in : Fin b → ℕ) (d t : ℕ)
    (p_in : ∀ j, 0 < w_in j) (pd : 0 < d)
    (balance : (∑ j : Fin b, w_in j) + d * (12 - b) = 2 * t)
    (nonneg : (0 : ℤ) ≤ ∑ X ∈ F,
      ((((∑ j ∈ univ.filter (fun j => e j ∈ X), w_in j) + d * (X \ univ.map e).card : ℕ) : ℤ) - (t : ℤ))) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  let w (i : Fin 12) : ℕ := (∑ j : Fin b, if e j = i then w_in j else 0) + if i ∈ B then 0 else d
  have w_pos (i : Fin 12) : 0 < w i := by
    by_cases hi : i ∈ B
    · obtain ⟨j, _, rfl⟩ := mem_map.mp hi
      have h1 : 0 < ∑ j' : Fin b, if e j' = e j then w_in j' else 0 :=
        Finset.sum_pos' (fun _ _ => by split_ifs <;> omega) ⟨j, mem_univ j, by simp [p_in j]⟩
      dsimp [w]; omega
    · dsimp [w]; rw [if_neg hi]; omega
  have sum_eq (X : Finset (Fin 12)) :
      (∑ i ∈ X, w i) = (∑ j ∈ univ.filter (fun j => e j ∈ X), w_in j) + d * (X \ univ.map e).card := by
    dsimp [w]
    rw [sum_add_distrib]
    congr 1
    · rw [sum_comm]
      calc
        ∑ j : Fin b, ∑ i ∈ X, (if e j = i then w_in j else 0)
          = ∑ j : Fin b, ∑ i ∈ X, (if i = e j then w_in j else 0) := by
              apply sum_congr rfl; intro j _; apply sum_congr rfl; intro i _; simp [eq_comm]
        _ = ∑ j : Fin b, if e j ∈ X then w_in j else 0 := by simp
        _ = ∑ j ∈ univ.filter (fun j => e j ∈ X), w_in j := by rw [← sum_filter]
    · have hno : X.filter (· ∉ B) = X \ B := by ext; simp
      calc
        ∑ i ∈ X, (if i ∈ B then 0 else d)
          = ∑ i ∈ X, (if i ∉ B then d else 0) := by
              apply sum_congr rfl; intro i _; by_cases h : i ∈ B <;> simp [h]
        _ = ∑ i ∈ X.filter (· ∉ B), d := by rw [← sum_filter]
        _ = d * (X \ univ.map e).card := by rw [hno, sum_const, smul_eq_mul, mul_comm]
  have tot : (∑ i : Fin 12, w i) = 2 * t := by
    rw [sum_eq univ]
    have huniv : univ.filter (fun j : Fin b => e j ∈ (univ : Finset (Fin 12))) = univ := by ext; simp
    have hosize : (univ \ univ.map e).card = 12 - b := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_map, card_univ, Fintype.card_fin]
    rw [huniv, hosize, balance]
  refine ⟨w, Finset.sum_pos (fun i _ => w_pos i) univ_nonempty, ?_⟩
  rw [tot]
  have nonneg' : (0 : ℤ) ≤ ∑ X ∈ F, (((∑ i ∈ X, w i : ℕ) : ℤ) - (t : ℤ)) := by
    simpa only [sum_eq] using nonneg
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at nonneg'
  have h : F.card * t ≤ ∑ X ∈ F, ∑ i ∈ X, w i := by exact_mod_cast (sub_nonneg.mp nonneg')
  linarith

theorem multi_weight_from_fibers {b : ℕ} (F : Finset (Finset (Fin 12))) (e : Fin b ↪ Fin 12)
    (closed : IsUnionClosed F) (empty : ∅ ∈ F) (full : univ ∈ F)
    (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (w_in : Fin b → ℕ) (d t : ℕ)
    (p_in : ∀ j, 0 < w_in j) (pd : 0 < d)
    (balance : (∑ j : Fin b, w_in j) + d * (12 - b) = 2 * t)
    (c : ℤ) (pc : 0 ≤ c)
    (bound : ∀ K ⊆ univ \ (univ.map e),
      let D := (univ : Finset (Finset (Fin b))).filter fun U => K ∪ U.map e ∈ F
      D.Nonempty → (if K = univ \ (univ.map e) then c else 0) - (if K = ∅ then c else 0) ≤
        ∑ U ∈ D, (((∑ j ∈ U, w_in j : ℕ) : ℤ) + (d : ℤ) * K.card - (t : ℤ))) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  classical
  let B := (univ : Finset (Fin b)).map e
  apply multi_weight_witness F e w_in d t p_in pd balance
  apply FranklGlobal.reassemble F B _ c
  intro K hK
  have sub := mem_powerset.mp hK
  let D := (univ : Finset (Finset (Fin b))).filter fun U => K ∪ U.map e ∈ F
  obtain ⟨_, _, top, _, _, sums⟩ := multi_slice_data F e K closed empty full minSize sub
  have eq : (∑ X ∈ F.filter (fun X => X \ B = K),
      ((((∑ j ∈ univ.filter (fun j => e j ∈ X), w_in j) + d * (X \ B).card : ℕ) : ℤ) - (t : ℤ))) =
    ∑ U ∈ D, (((∑ j ∈ U, w_in j : ℕ) : ℤ) + (d : ℤ) * K.card - (t : ℤ)) := by
    calc
      _ = ∑ X ∈ F.filter (fun X => X \ B = K),
            (((∑ j ∈ univ.filter (fun j => e j ∈ X), w_in j : ℕ) : ℤ) + (d : ℤ) * K.card - (t : ℤ)) := by
        apply sum_congr rfl
        intro X hx
        have z := (mem_filter.mp hx).2
        push_cast; rw [z]
      _ = _ := sums (fun U => ((∑ j ∈ U, w_in j : ℕ) : ℤ) + (d : ℤ) * K.card - (t : ℤ))
  rw [eq]
  by_cases nonempty : D.Nonempty
  · exact bound K sub nonempty
  · have ne : K ≠ univ \ B := fun same => nonempty ⟨univ, top same⟩
    have z := not_nonempty_iff_eq_empty.mp nonempty
    rw [z, sum_empty, if_neg ne]; split <;> omega

theorem fast_indexed_sum {b : ℕ} (D : Finset (Finset (Fin b)))
    (w_in : Fin b → ℕ) (fastW : ℕ → ℕ) (d k t : ℕ)
    (hw : ∀ m ∈ List.range (1 <<< b), (∑ x ∈ decode b m, w_in x) = fastW m) :
    (∑ U ∈ D, (((∑ x ∈ U, w_in x : ℕ) : ℤ) + (d : ℤ) * k - (t : ℤ))) =
      ((List.range (1 <<< b)).map (fun i =>
        (((fastW i + d * k : ℕ) : ℤ) - (t : ℤ)) *
          (if decode b i ∈ D then (1 : ℤ) else 0))).sum := by
  rw [FranklLocal.indexed_sum D (List.range (1 <<< b)) (decode b) _
      (decode_toFinset_univ b) (decode_nodup b)]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hw i hi]
  push_cast
  ring

theorem solve_row (b : ℕ) (F : Finset (Finset (Fin 12)))
    (closed : IsUnionClosed F) (empty : ∅ ∈ F) (full : univ ∈ F)
    (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (mi miExp : List ℕ) (pairs : List (ℕ × ℕ)) (genMask : ℕ)
    (w_in : Fin b → ℕ) (fastW : ℕ → ℕ) (d t offset : ℕ)
    (hcopy : HasCopy b mi F)
    (hExpEq : expandMasks mi pairs = miExp)
    (hGenOk : checkGenMask (1 <<< b) genMask miExp = true)
    (hp_in : ∀ j, 0 < w_in j) (hpd : 0 < d)
    (hbal : (∑ j : Fin b, w_in j) + d * (12 - b) = 2 * t)
    (hd_full : decode b ((1 <<< b) - 1) = univ)
    (hfull_mem : ((1 <<< b) - 1) ∈ miExp)
    (hw_m : ∀ m ∈ List.range (1 <<< b), (∑ x ∈ decode b m, w_in x) = fastW m)
    (hfiber : ∀ (e : Fin b ↪ Fin 12) (K : Finset (Fin 12)) (_ : K ⊆ univ \ (univ.map e))
      (D : Finset (Finset (Fin b))) (_ : ∀ U, U ∈ D ↔ K ∪ U.map e ∈ F)
      (v : ℕ → ℤ) (_ : ∀ i, v i = if decode b i ∈ D then 1 else 0)
      (_ : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F)
      (_ : ∀ i, v i = 0 ∨ v i = 1)
      (_ : ∀ a c, v a + v c - v (a ||| c) ≤ 1)
      (_ : ∀ g < 1 <<< b, isGen genMask g = true → ∀ u, v u ≤ v (u ||| g))
      (_ : ∀ (k : ℕ), K.card = k → ∀ i, 0 < k + (decode b i).card ∧ k + (decode b i).card < 4 → v i ≤ 0)
      (_ : ∀ (k : ℕ), K.card = k → ∀ i, i = (1 <<< b) - 1 ∨ (k = 0 ∧ i ∈ miExp) → 1 ≤ v i)
      (k : ℕ), K.card = k → k ≤ 12 - b →
      ((if k = 12 - b then offset else 0 : ℕ) : ℤ) - ((if k = 0 then offset else 0 : ℕ) : ℤ) ≤
        ((List.range (1 <<< b)).map (fun i => (((fastW i + d * k : ℕ) : ℤ) - (t : ℤ)) * v i)).sum) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  classical
  obtain ⟨e, hMi⟩ := hcopy
  have hExp : ∀ m ∈ miExp, (decode b m).map e ∈ F :=
    hExpEq ▸ expandMasks_mem e closed empty mi hMi pairs
  have hGenM : ∀ g < 1 <<< b, isGen genMask g = true → g ∈ miExp :=
    checkGenMask_sound hGenOk
  have hGenF : ∀ g < 1 <<< b, isGen genMask g = true → (decode b g).map e ∈ F :=
    fun g hg his => hExp g (hGenM g hg his)
  apply multi_weight_from_fibers F e closed empty full minSize w_in d t hp_in hpd hbal
    (offset : ℤ) (Nat.cast_nonneg offset)
  intro K sub
  let B := (univ : Finset (Fin b)).map e
  let D := (univ : Finset (Finset (Fin b))).filter fun U => K ∪ U.map e ∈ F
  change D.Nonempty → _
  intro nonempty
  obtain ⟨uc, _, _, smallD, fixD, _⟩ := multi_slice_data F e K closed empty full minSize sub
  have hD (U) : U ∈ D ↔ K ∪ U.map e ∈ F := by simp [D]
  have hunivF : (univ : Finset (Fin b)).map e ∈ F := hd_full ▸ hExp ((1 <<< b) - 1) hfull_mem
  have top : univ ∈ D := FranklGlobal.nonempty_full D nonempty (fixD univ hunivF)
  have cap : (univ \ B).card = 12 - b := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        card_map, card_univ, Fintype.card_fin]
  have hk_le : K.card ≤ 12 - b := (card_le_card sub).trans_eq cap
  have lo : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hi : K = univ \ B ↔ K.card = 12 - b :=
    ⟨fun h => h ▸ cap, fun h => eq_of_subset_of_card_le sub (by omega)⟩
  let v (i : ℕ) : ℤ := if decode b i ∈ D then 1 else 0
  have hv (i : ℕ) : v i = if decode b i ∈ D then 1 else 0 := rfl
  have bit (i : ℕ) : v i = 0 ∨ v i = 1 := by dsimp [v]; split <;> simp
  have du := FranklLocal.decode_union b
  have join := FranklLocal.indicator_join D uc (decode b) du
  have hgens : ∀ g < 1 <<< b, isGen genMask g = true → ∀ u, v u ≤ v (u ||| g) :=
    fun g hg his => FranklLocal.indicator_force D (decode b) du (fixD (decode b g) (hGenF g hg his))
  have exclude (k : ℕ) (hk : K.card = k) (i : ℕ)
      (bad : 0 < k + (decode b i).card ∧ k + (decode b i).card < 4) : v i ≤ 0 := by
    have hn : decode b i ∉ D := fun h => by have := smallD _ h; omega
    simp [v, hn]
  have stable (k : ℕ) (hk : K.card = k) (i : ℕ)
      (ok : i = (1 <<< b) - 1 ∨ (k = 0 ∧ i ∈ miExp)) : 1 ≤ v i := by
    have hmem : decode b i ∈ D := by
      rcases ok with rfl | ⟨hk0, hin⟩
      · exact hd_full.symm ▸ top
      · have hK0 : K = ∅ := lo.mpr (hk.trans hk0)
        exact (hD _).mpr (by simpa [hK0] using hExp i hin)
    simp [v, hmem]
  rw [fast_indexed_sum D w_in fastW d K.card t hw_m]
  have off_eq : (if K = univ \ B then (offset : ℤ) else 0) - (if K = ∅ then (offset : ℤ) else 0) =
      ((if K.card = 12 - b then offset else 0 : ℕ) : ℤ) - ((if K.card = 0 then offset else 0 : ℕ) : ℤ) := by
    simp only [hi, lo]; split_ifs <;> omega
  rw [off_eq]
  exact hfiber e K sub D hD v hv hGenF bit join hgens exclude stable K.card rfl hk_le

open BaseVec FTree CTree CertItem

def e0 : FTree := fl 0

def mi_7 : List ℕ := [15,23,27,39,43,51]
def miExp_7 : List ℕ := [59,55,63,47,31,0,15,23,27,39,43,51]
def mi_8 : List ℕ := [15,23,39,71]
def miExp_8 : List ℕ := [127,119,111,95,63,103,87,55,79,47,31,0,15,23,39,71]
def mi_12 : List ℕ := [15,23,39]
def miExp_12 : List ℕ := [63,55,47,31,0,15,23,39]
def mi_16 : List ℕ := [15,23,27]
def miExp_16 : List ℕ := [31,0,15,23,27]
def mi_26 : List ℕ := [15,23,47]
def miExp_26 : List ℕ := [63,31,0,15,23,47]
def mi_27 : List ℕ := [15,31,47]
def miExp_27 : List ℕ := [63,0,15,31,47]
def mi_28 : List ℕ := [15,23]
def miExp_28 : List ℕ := [31,0,15,23]
def mi_29 : List ℕ := [31,47]
def miExp_29 : List ℕ := [63,0,31,47]
def mi_30 : List ℕ := [15,31]
def miExp_30 : List ℕ := [0,15,31]
def mi_31 : List ℕ := [15,51]
def miExp_31 : List ℕ := [63,0,15,51]
def mi_32 : List ℕ := [15]
def miExp_32 : List ℕ := [0,15]
def wVec_7 : Fin 6 → ℕ := ![5,5,4,4,4,4]
def fastW_7 (m : ℕ) : ℕ := cond (bitAt m 0) 5 0 + cond (bitAt m 1) 5 0 + cond (bitAt m 2) 4 0 + cond (bitAt m 3) 4 0 + cond (bitAt m 4) 4 0 + cond (bitAt m 5) 4 0
def cFn_7 (k i : ℕ) : ℕ × ℕ := (fastW_7 i + 1 * k, 16)
def rowZ_7 : ℕ → List ℕ
  | 0 => (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowO_7 : ℕ → List ℕ
  | 0 => (unpackBytes 11 0x403c3834302c28201c1810)
  | _ => []
def cp_7_0 : CertItem := CI none 0x117177f177f7ffe 0x8888888088808000 e0 (W 0)
def cp_7_1 : CertItem := CI none 0x101170117177f 0x8000000000000000 e0 (W 0x31eb20021eaa0021ea60022e9a0022e960012e8e0031e720021e6a00236660022e5a0014e560012e560021e3a0022e36001562e0011e1e)
def cp_7_2 : CertItem := CI (some (BV 0x1c00001700001700001200001800001300001300000e00001800001300001300000e00001400000f00000f00000a00001800001300001300000e00001400000f00000f00000a00001400000f00000f00000a00001000000b00000b00000600001800001300001300000e00001400000f00000f00000a00001400000f00000f00000a00001000000b00000b00000600001400000f00000f00000a00001000000b00000b00000600001000000b00000b00000600000c000007000007000002 0x10000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010 960 1024)) 0x100010117 0x8000000000000000 e0 (C 12 (C 20 (C 24 (C 36 (M 2 0x2609500660250045825001381500232150022ec60042ec20021eaa0021ea600c36a20022e9a00a1e8a0082e860021e860031e720021e6a0021e5a0021e560032e4a0071e4a002564600836460021e3a0021e36002662a008562a0084e1a0022e1a0032e160041e16008660e) (W 0x2709100164910016291001549100252910026025001422500260150015015001381500132150044e920082e920031e920051e8a00436860011e720011e6a0011e5a0011e560012e4a0041e4a001564600436460011e3a0011e36001662a004562a00266260032e1a0021e1a004660e)) (W 0x152610014c610014a610024861003446100138250012a25002501900330190016015003501500130150041e920021e8a0052e86008566200436620081e620012e5a0024e4a0032e4a00466460014e460011e3a0011e36001562a0024e2a0021e2a00356260044e0e)) (M 2 0x2525100244510023451002504900438490036845001584500650450024a25001482500628250046019002541900450190047015003601500358150021e9a0084e920031e92008568a00a1e860023666006566200636620104e520082e520101e52004664a0021e3a0021e36006662a0041e2a0014e26004760e004660e)) (M 2 0x35c510024c510065049007424500238350026431009623100460310025231009443100234310032231003282900138250047019004601900138190046815002601500458150022ec20024e9600c2e920012e8a0034e86002566600c56620022e5a0022e560042e52004664a0104e320102e320081e32007562a001562600836260014e1a002760e004660e0024e0e))
def cp_7_3 : CertItem := CI (some (BV 0x1d00001800001800001300001900001400001400000f00001900001400001400000f00001500001000001000000b00001900001400001400000f00001500001000001000000b00001500001000001000000b00001100000c00000c00000700001900001400001400000f00001500001000001000000b00001500001000001000000b00001100000c00000c00000700001500001000001000000b00001100000c00000c00000700001100000c00000c00000700000d000008000008000003 0x10000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010 1024 1024)) 1 0x8000000000000000 e0 (C 16 (C 4 (C 8 (C 32 (M 2 0x142710034461007426100a1ea20022e920081e920052e8a0011e7200a2e52002364a0061e4a00836460012e320091e32008562a0082e26008661a0084e16002560e0024e0e0023e0e003760a0036e0a00a660a00f76060011e06) (M 2 0x842610012831004501500270090026805002580500244050033805002240500214050020c0501236820122e820121e820021e620092e520061e4a00836460091e32006562a0082e260044e1a002361a0044e16004560e0024e0e00a660a002360a0012e0a0011e06)) (W 0x15851001423100224310044829003602500148250012821002301900250150023015001100d00170050016805001440500238050032e520022e4a0044e46009662200556220094e2200536220092e220051e220024e1a0026e0e0036e0a005660a0034e06)) (M 3 0xa4451001504900740450074825005282500b64210045019008301900550150073015007621100460110055011003080d002680900b600900858090033809003700500568050024405003240500314050143682008364a00166460043646006562a003362a0076622009562201b661201b561200f4e1201b361200f2e1200f1e12006660e0086606)) (M 6 0xe4451010425100c504900a584500e40450035c410025041002484100444410084241012603100c243100b4029018482500464210186221004482100a601900e5019018301500d54110063011006200d006140d006080d0087009002500900c380900868050026005006440501b56820014e8201e664203656420364e4201e364201e2e420361e420071e2a0164e2201d4e12003560a0171e0a0205e06))
def cp_7_4 : CertItem := CI (some (BV 0x1e00001900001900001400001a00001500001500001000001a00001500001500001000001600001100001100000c00001a00001500001500001000001600001100001100000c00001600001100001100000c00001200000d00000d00000800001a00001500001500001000001600001100001100000c00001600001100001100000c00001200000d00000d00000800001600001100001100000c00001200000d00000d00000800001200000d00000d00000800000e000009000009000004 0x10000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010000010 1088 1024)) 0 0x8000000000000000 e0 (C 0 (M 2 0x114110026005002500500248050040c050061e8a0061e860082e820081e820081e620084e52006364a006564600b2e420051e420081e320052e2a0063626004662200c56220021e1a0046616002361600c4e120012e120021e12004660e006760a008660a0047606) (W 0x114110011211002080d0014809001300900128090022209002120900160050015005001480500244050013005001280500a760200a6e02006660200a5e0200656020064e0200a3e0200636020062e020061e02))
def cp_7_5 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x71e820031e620031e520021e4a0021e460062e420031e320021e2a00236260024e2200536220011e1a0014e160011e1600256120054e120014e0e006560a005660600156060096e020026602)
def cp_7_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x21e520011e4a0011e460061e420021e320011e2a0011e260022e220041e220012e1a0012e160062e12005360a0024e06003360600456020064e02)
def wVec_8 : Fin 7 → ℕ := ![8,8,8,6,6,6,6]
def fastW_8 (m : ℕ) : ℕ := cond (bitAt m 0) 8 0 + cond (bitAt m 1) 8 0 + cond (bitAt m 2) 8 0 + cond (bitAt m 3) 6 0 + cond (bitAt m 4) 6 0 + cond (bitAt m 5) 6 0 + cond (bitAt m 6) 6 0
def cFn_8 (k i : ℕ) : ℕ × ℕ := (fastW_8 i + 2 * k, 29)
def rowZ_8 : ℕ → List ℕ
  | 0 => (unpackBytes 63 0x71696563626159555352514d4b4a494746454443424139353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 29 0x6151494543424131292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 8 0x4121110905030201)
  | 3 => [0]
  | _ => []
def rowO_8 : ℕ → List ℕ
  | 0 => (unpackBytes 15 0x807870686058504840383028201810)
  | _ => []
def rowFl_8 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 22 0x71696559554d000071696359534b000071696259524a000071636253524400006963624b4a4400005953524b4a440000555352474644000071595539351d000069594d392d1d000069594b392b1b000071595239321a000069594a392a1a00006252463226160000634b472b270f0000594d4b1d1b0f0000392d2b1d1b0f0000554d471d170f0000352d271d170f0000624a442a240c000063474427240800006246442624080000322624161408)
  | 1 => (unpackForbs 30 0x615149312919000061514531251500006151433123130000615142312212000061494529250d000051494519150d000031292519150d000061494329230b000051494319130b000031292319130b000061494229220a000051494219120a000031292219120a0000514543151307000031252315130700004945430d0b0700002925230d0b0700006145422522060000514542151206000031252215120600004945420d0a0600001915120d0a0600006143422322040000514342131204000031232213120400002923220b0a0400001913120b0a040000454342070604000025232207060400000d0b0a070604)
  | _ => []
def rowFbs_8 : ℕ → List (List ℕ)
  | 1 => (rowFl_8 0)
  | 2 => (rowFl_8 1)
  | _ => []
def cp_8_0 : CertItem := CI none 0x101170117177f0117177f177f7ffe 0x80808080808080808080808080808000 e0 (W 0)
def cp_8_1 : CertItem := CI (some (BV 0x3200002a00002a00002200002a00002200002200001a00002c00002400002400001c00002400001c00001c00001400002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00002600001e00001e00001600001e00001600001600000e00002000001800001800001000001800001000001000000800002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00002600001e00001e00001600001e00001600001600000e00002000001800001800001000001800001000001000000800002600001e00001e00001600001e00001600001600000e00002000001800001800001000001800001000001000000800002000001800001800001000001800001000001000000800001a00001200001200000a00001200000a00000a000002 0x1d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d 3328 3712)) 0x100010117000101170117177f 0x80000000000000000000000000000000 (N (N (N (N (N (fl 0x322624161408) (fl 0x5953524b4a44)) (N (fl 0x634b472b270f) e0)) (N (N (fl 0x352d271d170f) (fl 0x71696359534b)) (N (fl 0x69594b392b1b) e0))) (N (N (N (fl 0x634744272408) (fl 0x716362535244)) (N (fl 0x69594a392a1a) e0)) (N (N (fl 0x392d2b1d1b0f) e0) (N (fl 0x71595539351d) e0)))) (N (N (N (N (fl 0x624644262408) (fl 0x6963624b4a44)) (N (fl 0x625246322616) e0)) (N (N (fl 0x554d471d170f) (fl 0x71696559554d)) (N (fl 0x69594d392d1d) e0))) (N (N (N (fl 0x624a442a240c) (fl 0x71696259524a)) (N (fl 0x71595239321a) e0)) (N (N (fl 0x594d4b1d1b0f) e0) (N (fl 0x555352474644) e0))))) (C 76 (C 41 (C 100 (C 50 (C 13 (C 25 (C 105 (C 14 (C 113 (C 42 (C 92 (C 112 (C 56 (M 2 0x2a949006f145008c545002a471004924d002724d002464d002344d006c22d002b42d002942d0022fd20022fca0021fb20021faa0111fa20054f8a0071f860021f660121f620092f520031f520044f4a0062f4a00b1f2a0024f260072f260068f1a0041f1a0044f160032f160031f160094f0e0021ef20021eea00e1ed200e2ec600e1eb20024e9a0042e9a0041e9a0044e960063e96008ae8e0064e720061e7200c1e6a004ce5a0062e5a00ace560061e1e0010047) (W 0x174e5001e8e1004a8e1005a4e1005a2e1004704d003f02d002702d0012fca0011faa0061fa20042f8a0041f860011f6a0011f660091f620022f520012f4a0012f460041f2a0044f260041f1a0038f160014f160011f0e00f1ee20072ed20078ec60071eb2002ae9a0038e9a0058e960034e8e0021e8e0071e720048e6a0021e6a0024e5a0032e5a0058e56001ce4e0031e1e0030047001003f)) (M 2 0x2f1d1002f1c900ee145002f125006e0b1004e09900ae09500ae059002624d002344d00ae02d01e2fc20021fb20021faa00d1fa20044f8a0051f8a00e4f860021f6a0021f660071f620081f520092f4a0091f2a0084f260041f260018f1a0092f1a0058f160051f1600a3f0e0021ef20021eea0021ee600c1ee20082ed20062ec60061ec60081eb20064e9a00a1e8e0064e720021e7200c1e6a0062e560041e560019e4e0054e4e0061e1e0050053006003b)) (M 24 0x18b965018d545060b945018a945018a545043b929048f125030b925018b0e9018b0e5078b8e1065b869018464d018344d015c22d018b42d047b02d0182fd20182fca0772fc20181fb20771fa20471f8a0931f861681f720902f5201d4f4a0112f4a0041f2a0301f260488f1a0301f1a0784f160044f0e0741f0e0181ef20601ee20a82ed20a48ec60a81eb20484e9a0301e9a0743e9605c8e8e00d4e7209b1e7202b4e6a0304e5a0482e5a0378e5603d1e560445e4e0041e2e0441e1e06100530040003)) (M 2 0x2b2a900ab0a900ea8a900ea2a900e92a900278a900272a900258a90027099002689900a544d004f02d002e42d002622d002462d00b2fc200e2f860021f720021f6a0071f4a0071f2a00a1f1a0068f160042f160092f0e0011f0e00c2ed20058ec60062ec601e8eaa01e2eaa0121eaa0064e9a00a8e960088e8e00e1e7200e8e6a0049e5a0062e5a0019e560058e560041e560061e1e0070053)) (M 5 0xff1c5002e9c5005e565021e351003e94901be349006c32901ca329019e0a9008e08d009e071023e269005d42d001b02d004a42d00f702d04b2fc602c1fa201f1f8a0164f860051f720051f6a0281f620231f260172f1a0082f1600a1f1600f8f0e0082f0e0051ef20051eea0051ee601b1ee20211ed201c2ec60231eb200a1eaa0178e9a0122e9600f4e8e0181e720199e5a0121e560068e4e00f2e4e0031e4e00f1e1e0010053002003b0070027)) (M 3 0x3e2b1003b8b1003b2b1003a8b100372b1006a4a9007c4690085469009f039003e839003e439007e039003d839003d439003b439012a839003783900b74390077039003583900f702d00d4f1a0028f1600c4f160122ed20158ec60028e9a0094e9a005ae960092e9600dae8e00c8e5a00f8e56006ce4e0092e4e02dce3a02dae3a01b8e3a02d6e3a01b4e3a01b2e3a0091e3a0078e1e005005300b004f004004b00400470050043005003300100230030013)) (M 4 0x3d5a5014d351004d945014d34500cf10d005d30d004d0e901cd2b1014d28d01cd271014d24d008d039014622d0042fd20042fca0042fc60162fc20351fa60071fa200b2f8a0194f860041f720041f6a0041f660161f620081f5200e4f4a0031f4600b1f2a0191f260142f1a0034f160102f160041ef20041ee60241ee201c2ed20018ec60072ec600c2eaa0101eaa0141e9a0088e9600c4e9601c1e6a00f9e5a0045e5a0014e5a00c2e560081e5600c1e3a00c8e1e00e00530030047)) (M 12 0x1f349013f149004e34900ca8e100cd271030c27100c7271029d06901fc26900ce86500ce46500cd86500cd46503dd065054c46500cb86500cb465048a86503ca46500c786500c746500c386500c3465010e02d00cb22d011702d0541f2a04f4f2603c2f1a00c8f160302f160188f0e0246f0e0542ed20541eb20548eaa0244e9a0181e9a0388e960039e8e0348e8e0b48e660b44e6606c1e660184e5a0242e5a038ce56038ce4e0188e3a0241e3a00ece2e020ee1e005004f04f002f0040003)) (M 5 0xaa8a901e5869005386900ac465014a465005746500ff035005e835005e235017e035017d03500cc235005b835005b235019a835005923502d7035005583501e3835005d22d00fb02d005922d0184f1600f8f0e0092f0e0232ed20238ec60158e960014e960022e96018ae8e006ce5a0138e5a0118e560084e5600ace4e00f2e4e04bce3604bae3602d8e3604b6e3602d4e3602d2e3600f1e3600e4e1e016004f01900230010007)) (W 0x1e3a1001d585004d185001c585001a545001c329001a519005e115001e8e10048ce1002f0d100470d1001d8c9005d2c9001b8c9001b4c9001b2c9002b0c9007a8c9006a2c900294c900792c900578c900172c900168c9001f0c5003b0c5001a4c500174c500164c500364650021f8a0051f0e00f8eca0092eca00f1eca0071eb20078eaa0034e9a0021e9a0019e960048e960058e8e0071e720058e6a0021e6a0048e660028e5a0032e5a0058e560039e4e0028e4e0028e3a0031e3a003ce360028e36002ce2e003ae2e0038e1e0040053)) (M 2 0x1e5c5001e5a1001e3a1006f191007e191003d591003d191002d389001d189002c989002c969002c965005d945009c945009e929004c92900ac925002c8e9002c8e5004c8e1009c4e100ec8c9009d0c5005c8c5002c89500dc86900ec865001e04d003d04d007c839004c83500ae02d01e1f9200e2f860021f720121f6200a4f520041f520082f4a0061f4a0041f2600a2f1a0068f160041f1600a1f0e0021ef20041ee200e2ed200d1eb200c2eaa0011eaa0064e9a0041e9a0088e9600a8e8e00d4e72006ce5a0044e5a00a1e560062e4e0022e3a0062e360061e1e001001b)) (M 12 0x1af19100ce38900cc98500cc585021c561026b12902ea329022c8e100cd2d1003c2d101bd0c9001b2b104770b100af0ad0328ca900c72a900ce8a500ce4a503ce0a500cd8a500cd4a500cc8a5015c4a502fb8a5032b4a5054a8a5054a4a503c8aa503386a505378a500c74a500c58a501654a5022e095001709500bb271023b071026a27100e2fc20354f8604e1f260058f1a0452ed20398eca0548ec60b48ea60b42ea606c1ea60138e9a0244e9a019ae960248e8e00f2e8e0548e6a03c8e660161e660184e5a0242e5a00c9e560308e5603c8e4e018ae3a0241e3a01e8e3601e2e360382e2e01f8e1e002002b004000f005000b)) (M 5 0x2e9a9005d371005a945005e531005e331019e131003d531020c531023c331005b53101aa531001a331010e129005b329004a929005992900ff125003e925003c525009a5250059925007d10d00598e900598e502398c902398c500ab0a500ba8a5005d869008d06900dc869001c8650229865011c859013b04d019d02d01d2f4604b4f3204b2f3202d1f320166f1a0196f1600f8f0e0036f0e0051ef20281ee20232ed201e2eb201f1eaa00e1ea6019ae9a0148e960052e9600a8e8e00f4e8e0161e720054e5a00a8e5600f2e560068e4e00d1e3a0172e360021e3600fce1e00400570010037005001f004001b0030017))
def cp_8_2 : CertItem := CI (some (BV 0x3400002c00002c00002400002c00002400002400001c00002e00002600002600001e00002600001e00001e00001600002e00002600002600001e00002600001e00001e00001600002800002000002000001800002000001800001800001000002e00002600002600001e00002600001e00001e00001600002800002000002000001800002000001800001800001000002800002000002000001800002000001800001800001000002200001a00001a00001200001a00001200001200000a00002e00002600002600001e00002600001e00001e00001600002800002000002000001800002000001800001800001000002800002000002000001800002000001800001800001000002200001a00001a00001200001a00001200001200000a00002800002000002000001800002000001800001800001000002200001a00001a00001200001a00001200001200000a00002200001a00001a00001200001a00001200001200000a00001c00001400001400000c00001400000c00000c000004 0x1d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d 3584 3712)) 0x10000000100010117 0x80000000000000000000000000000000 (N (N (N (N (N (fl 0xd0b0a070604) (fl 0x514543151307)) (N (fl 0x1915120d0a06) (fl 0x51494519150d))) (N (N (fl 0x2923220b0a04) (fl 0x31292319130b)) (N (fl 0x614542252206) (fl 0x615145312515)))) (N (N (N (fl 0x454342070604) (fl 0x51494219120a)) (N (fl 0x312522151206) (fl 0x615142312212))) (N (N (fl 0x514342131204) (fl 0x61494329230b)) (N (fl 0x4945430d0b07) e0)))) (N (N (N (N (fl 0x252322070604) (fl 0x31292219120a)) (N (fl 0x4945420d0a06) (fl 0x61494529250d))) (N (N (fl 0x312322131204) (fl 0x51494319130b)) (N (fl 0x2925230d0b07) (fl 0x615149312919)))) (N (N (N (fl 0x1913120b0a04) (fl 0x61494229220a)) (N (fl 0x514542151206) (fl 0x615143312313))) (N (N (fl 0x614342232204) (fl 0x31292519150d)) (N (fl 0x312523151307) e0))))) (C 33 (C 66 (C 12 (C 67 (C 10 (C 65 (C 68 (C 6 (C 34 (C 70 (C 42 (C 36 (C 97 (C 25 (C 84 (C 96 (C 14 (C 104 (C 24 (C 40 (C 48 (C 72 (M 2 0x8a525002a12500152150063815006700d006620d006340d0042fc20074f920031f9200a4f8a00e1f620021f4a00a1f460102f420081f4200a1f3200a1f2a0044f160021f160081ee200a1ed200a1eca0042ec600a1eb20098ea60064e9a0044e960021e960061e8e0041e720041e6a0062e5a0064e560068e5200c4e520041e520061e4e010ce4a0065e4a00ece460042e460041e460061e36002ce2e0044e2e014ce260021e260021e1e001ce1600a8e16) (M 2 0x499250069525002c921002c521002a521002a321012222500252150063815006620d005520d006340d0084f920084f8a0024f420162f420224f220222f220161f220064f1600e1ee200a1ed200a2eca0042ec600a1eb20031ea60064e9a0044e960021e960061e8e0041e720041e6a0062e5a0064e560045e520024e520022e5200e1e52006ce4e016ce4a004ce460061e360066e2e0041e260022e1e00a8e160015e0e)) (W 0x2a2e1003a2c9003b0c5001a4c5001a4c1001924900190490017049003684900162490033849001f045001e045001b045003a445001704500268450026445001a01500270150016015005e00d003b00d001700d0054f920054f8a0051f320051f2a0034f260011f2600c4f220032f160118ec200b2ec20111ec20051eb20028ea60031ea60034e9a0018e960024e960031e8e0028e720051e6a0022e5a0011e5a0032e560039e520088e520039e4e0011e4a0031e36002ae2e0011e2e007ae260042e260011e1e0058e16)) (W 0x5a2a100194a100192a100d90a100168a100162a100258990025095005524900150490013849001f045001e045001b045003a445002944500358450067015005b00d001700d003500d0054f920054f8a0051f320021f2a0041f260038f160042ed20052eca0048ec600d8ec20118ea20112ea200b1ea20014e9a0018e960034e8e0041e720051e6a0032e5a0024e560012e5600b8e520019e4e0021e4e0039e4a0012e4a0031e360021e2e00bae260014e1e0028e16)) (M 4 0x149869004a461004a26100458610045261009a051004905100c4a51004a24d008304d00e9249004704900c6849002624900c384902c3045004302d02c3025014701500c3015016b00d008a00d002920d004700d0144f920144f8a0232f420141f2a0044f260184f220181f2200c8f160082ed20142eca0108ec60022ec60348ec20101eb20101ea60288ea200c1ea20048e9a0084e9a00c4e8e0448e620444e6202c1e6200c2e5a00c4e560098e520024e520082e5200c1e360081e2e0048e1e0048e16)) (M 2 0x1d189001d129002e0c9008d0c9002e0b1002d0b1006d099004d08d006d071002b071006d069002b069006d059006d055002e051006d051004a05100892510025051006d04d00668490025049002e04500ed04500290450043045002f02d002e02d002302d002d025004242500ab0150013015004e00d00ed00d0201fa200a4f920094f8a00a2f4a00a2f460144f420022f4200a1f320091f2a0024f260152f220031f220038f160034f1600e1ee20041ed200a2ec600e8ec200c2ec20062eb200a2ea60161ea20064e960024e8e0021e720021e6a00d8e620061e6200a2e4a0061e3600c2e260041e260024e1e0078e16)) (W 0x23045001f039007e039007d039002c439009a03900390390056439004603900350390032c390036235003222d00b3025002681500350150033815004700d002600d003500d0054f920034f8a0038f160022ec60072ec20034e9a0018e960024e96001ae8e0028e8e0018e560024e56002ce520098e52003ce4e00bce4a0018e460052e46011ce3a011ae3a00b8e3a0116e3a00b4e3a00b2e3a0051e3a0018e1e0018e16)) (W 0x2c989002c961002d149001c149001b149002c545001c145001c941001b131001c129004e125001a125001c4b1001c0b1001a4b1002a2b1003e0a5001c099003c095001c08d005c071005c069003c059002c055001625500ba051003c04d003c039003c035004c02d001c025004682500160250016815001601500252150033015001f00d005d00d002c00d001500d00b4f820112f820111f820031f620042f320042f2a0022f2200b1f220038f160071ee20051eca0041ec600b2ec20012ea200b1ea20024e9a0024e8e0058e620051e6200b8e4a0052e460061e460051e260014e1e0028e16)) (W 0x2c561001f151006d151005c951003c551001c151003b151001d149001c149003a949003a945002a545001a929001a129005a925005a8c9004a8c5001a0c5005a8a5003a08d005a8690036055002b04d001a04d002a049005e845002b845003a839003a02d007e025002a825001a02500470150033815003700d003600d003300d00b4f820114f5200b2f520091f520011f420054f320034f2a0024f2200b1f220038f160051ed20022ec20051ec20051eb20078ea20061ea20024e9a0034e960021e720038e620074e620031e5a0049e520012e520061e520094e4a0042e460031e360011e1e0028e16)) (M 12 0xcb07100c707100cf069006e069009d069008b06900da26900c706901ee065033c865035c465036c06500cb06503ca86503ca46501f8a6500c706503c646501a58650244a6502446650243865009c8610033059011b05500ce05104bd051024e04d024a249004904901468490246249024324900cc04501f684500c3039024502d0249825024942500a6825022582502470150056015007c40d023b00d00c700d05a4f8200b4f4602b4f420712f420184f320184f2a03c4f260244f220741f220058f160182ec60978ec203c8ea60781ea20244e9a0cc8e660cc4e660841e620212e5a0138e560134e5201b2e520594e460181e3a0241e360108e2600c4e1e0378e1600c5e1602ace0e00c4e0e)) (M 4 0x4d191006e989002c989004f185004d18500cc98500cc585002c961018c361014d151014c349004c341006e13100ec331014c329002a32500ac2d100ac0d1010c2c9004c0c9014c2b100362a5002e09900ac099014c271014c26900cc05900ac255002a055010c25100aa25100ae039002c03900ae035002c23500cc22d0177015005521500ca00d00c920d00c520d02c4f860442f860441f860061f460142f420061f260261f2200c8f160051ee20112ec60261ec20261ea200c4e960044e8e0082e8e0148e660268e620121e5200c1e4e0195e4a0134e4a0188e460142e46004ae260064e2600e2e260141e260044e1e0088e1600e0077)) (M 8 0x970d1010d0c5008c4c1008c2c102e90c1025c0b5008c4a1008c2a100b709900d5099018d095038f091008e091008d091018c491018c291020a29101862910285291010e08d01e486901d4865002c061018a451008a251020925100a3451015c04d001604d002504d01f58490085049018484900e384900b3249008d045028c8450176445009584500850450186835015602d003302d020e0250076825011642500846250183825018901500370150155015018c00d020700d010500d0381f620281f520102f4a03a2f4201a1f420281f320281f2a0081f2600e2f220188f16088ae920889e920588e920284e920883e920582e920581e920021e7204e1e620182e5a0102e560081e5600e8e520181e3a0081e1e0108e160081e160140077)) (M 10 0xae189002d4d1032d4c5025a0b102be0a903ed0a9032c8a9028c2a9032a8a9032a2a9048a0a902898a903292a900a70a903068a900d58a902df4a5005f0a500ac2a100a98a100d8aa1004a48d00ab07101e547100a507100ab069028c06500a506500c545901e5055002644d01e484901a4649008d04500c944505a5445011503900ac035008b035011e02500ab02502ea42501e542503c701501e5015005f00d01ec00d020b00d0284f8a00a4f820282f820152f420261f2a03a2f220481f220118f160302eca0828ec20aa8eaa0aa2eaa06e1eaa01e2e9a01e8e9601e8e920324e920288e6a03b8e620471e620128e5a0478e520271e5201c2e4e0204e4a0162e4a00dae3a00d1e3601e1e2e0071e2600a8e1e0178e0e)) (M 12 0x33a329005a129021c92500cc12500ca12500cc521010c12100ca921007a521018a12100cf119054e119055d119024c11906cb119024a119021991900395190488ce10188cc10178cb100a325500fd05100cc05101f8a51002625103c525100c5051009544d01b344d00cc44903cc249009a249003924900c6249024384901bc84500cc045005a84501b984500c7045018644501838450104839026a035024c42502ba825035a4250249015022601502450150023015024c00d01ba00d024900d009300d0131f820b95f1e0844f1e1798f1a0cc3f1a0842f1a0841f1a0056f1603c1ed20242eca02e8ec60198ec203c2ec20251eb20332eaa05f1ea20242e9a024ae96038ae9203c4e92024ae8e0214e6a0324e660841e620025e5a0222e5a01a2e560141e3a0241e2e0087e1e0041e1e00d0077)) (M 4 0x4ed21004a52100dc0d5004c2c100464b100460b100c64ad00860ad00866a900ecca1004c8a1004c2a10086ca100c749900cc095014e491004e091002d491004b09100c749100ca08d004f089018e089006d089010c88900cc289018b089014a889014a2890149889014928900a8c8901c70890146889014628900c58890145289005c465004446500bc05500c384900b3249016d045004c445004a4450045045002484500838450079439005c0350076035005c02d00bc42500ca425004a0250046425017601500c50150013015008a00d00c900d00c540d001300d0161f4200d1f2a01a1f220028f1a00c8f16044ae8a0449e8a02c8e8a0144e8a0443e8a02c2e8a02c1e8a0148e6a02c1e6200c2e5a0012e5602c8e520059e4e0072e4e0159e4a0058e3a0071e2e00d1e260048e1e0028e0e0060077)) (M 120 0x3b586907850691e0a8650368a6501450650f34a6107848610f0cc590789c5908a98550de5055239c251078c0510f0a25107898511045251168944d0c7a2491239249078904916862491545249040c04507890450788a45163584515b384513a344503bc039078a8390b56c390aea0350ba8a3501fc22d0bda02d08c622d0f0a425258642506462250ae48250cf4425078f019348e019348d019168c8190f0c419348b019168a4190a998190bd941907b9019348701925068191bf54190fd381906b34190f0c815078c0150ae9815008681516060150ba5815168c40d0a1a20d033940d135920d099540d02e320d7f8ee1a7f8de1a528ce1a7f8be1a528ae1a5289e1a2588e1a7f87e1a5286e1a5285e1a2584e1a5283e1a2582e1a2581e1a4ad007700a003f)) (C 34 (M 10 0x7fcf5d00cc349012a929002a129014c521008c321022ab21008a521015b11900af11100ae11100ad511024d11101ec51101ec31100bb11101ea511040a31101e95110098ce10018ae103c88e103292d1015b0c901d88c903288c503288a9002c0a503088a501d8aa100da89900ba099011b09500da89501ea08d031c069001b869032886501bc055003385501e904d025c84900ac049032984901ad845022d04500ac04500ea04501ec039018e035006a83501ea02d024e02500dc82500aa02501e882501e601901e601501e501501b301501ea00d01e900d01e600d0328f120aa5f120ed4f120aa3f120ed2f1206e1f120108ec20161ec20321eb200b2ea203c1ea20064e9a06c2e9202f1e720284e6203f1e6201cce5a0024e5a03a5e520322e5200d5e4a01a5e460151e2600a4e1e01f4e1a01d1e1a0034e160020073) (M 60 0x3c909104e8a91113749103c709107862910435291016e08d016c08d088908d09ec2891a4b08912ca88912ca28903ca08912c988903c948912c92890fc888914f70890b768890b462890b458890b4528903c606501e58650d244650d5c86103c88610b44a6101460550a0505504cd051048cc51052c45108ec25103cc0510af545103552510b4504d057c84903c90490b4884905a584905f38490dac44503cc04504d94450b4884507d544507150350dba02d03cc0250f3a42503ca0250b4882507568250f0d0190b4901918ee015066c015028601503cf00d068d00d039a40d072a00d0a3940d011900d019700d12c8f123fc3f122942f122941f123fcae8a3fc9e8a2948e8a12c4e8a3fc3e8a2942e8a2941e8a0cd1e7212c1e6a0b42e5a0941e4a0072e3a0ad1e3a0431e3603c1e1e0782e1a1470077))) (C 5 (M 60 0x78c14d02ed141078c741078e13103cc12903ca32901ba12903ccb25026cb2115dab210b4e1190fed1150f3f111008e11103cd11103fb31103cb1110999511026e90503ce10503cd105116c90512cc50512fb10512ca90512ca5050b4990504a89051a482e112c82d112c82c9070a2b10bc82b112c82a90b4a0990b4b295039b09105aa09103ca0890f0928912cc27112c8269088c0610b490590b4c0550e582510b4904d021904903c50490b448490b446490b43249016c84503c50450b44845068c03904ca039034e035080a2350b4822d099482504a44250b428250b4c0190b4a01904c5019068301921c820d12c8f063fc6f063fc5f062944f063fc3f062942f062941f0612c2ec606d2ec229f1ec212c1ea60e02ea21681ea211e4e8a0781e6621c1e620fb4e5201b2e4a07d5e461112e460fe1e2600e4e1e02e1e1e) (M 10 0xa82a1008a899006a49900aa09500aa891004989100a92910069091014a289009a08900a928901e888901e828900b5889008c07100f64710104c710158c69014826900a6869032c26501b4661010985900e885900ac8550149255018945100a90510098c5100a58510145451002c04d014524d008504d00a9049004884901e824901b624901d584900a5049032c44500ac04501a944500a924500a5045003464501ea83900ac835014623501e822d02ca425023642501e5425002a81901e901901e68190135019009381900af015046e015046d01501ec815046b01501ea21501e9815046701500a6815014601501e5215002381501c301505a820d0aaee160aade1606ece160aabe1606eae1606e9e160328e160aa7e1606e6e1606e5e160324e1606e3e160322e160321e1604900770250073001004b))) (C 36 (C 70 (C 68 (C 98 (C 48 (M 12 0x5496e1024a4ad006b2a9033b2a102f94a100654790088a7100a507100b9069021d06500d94610699061002586100658490244c49018464901c984501c8a450105845030544500c50450246439024b035024b02d00cf029048e02903cc82903cc22900dc02903ca82903ca229020982903c922903c822903c682900c642903c6229024582903c522900c462902a382901b32290092629030d425003d02500cb425045b025030d019008c019030b0190049019024901502450150243015024c00d018a40d00ca00d018820d00c640d00c2fc20634f8207e4f420122f420308f060218e960032e9603c4e8a0482e8a0038e5a0212e5a0248e5604b8e520394e5201b2e4e042ce4a0ccce2a0ccae2a0848e2a0cc6e2a0844e2a0842e2a03c1e2a00c8e1e) (M 4 0xc96e101696c100496a900992710049071004607100ca059005905500750550085251007d04d003a04d002904d004c0490079c49008824900e94450049045009584501054450015045001d03900bc03900c603500cd02d004f029018e029004d029014c829014c229005b029014a829014a229013982900b9229020822901468290146229004602900b582900c52290014c2900c322900c2829004e025004d0250019825006942500b8a25003602500c4a250033825008b019010701900c601900fb01500c60150093015001a40d003820d00c600d0132f4a0012f160148eca0308ec202c2ec200b4e9a00c8e8e01e8e8a0094e8a0188e520122e4a044ce2a044ae2a02c8e2a0446e2a02c4e2a02c2e2a0141e2a002ce1e0022e1e0148e0e02500770060053)) (M 4 0x7c465002966100c8a61004586100c5055014c451004c05100490510095451007525100cc44d004c449001984900696490068249002584900c4c490049045002584500b544500c4a4500b444500cb03900b7035004f02d008b02d01ce029014c829004c429014c229004b029014a829014a22900c9829014922900470290146829014622900c582900d522900c382900c3229002d025010c425002c0250079825004702500564250083825010d01900cc419003b019005701900ad01500cc01500590150047015006501500cc40d006a00d012820d01f4f8a0442f8a0142f4a00c2f420148f0600f2eca0112ec200c2e8e00d8e8a0144e8a00c2e5a00c8e4a0042e46044ce2a044ae2a02c8e2a0446e2a02c4e2a02c2e2a0141e2a0042e1e0220077)) (M 6 0x21d941006c54100bc511006a51100dc505012a5050249ce101e88c90369cc100998c100688c100398b501a88a90128aa102788a1006e099007c099005a0990129895006826900c526901a886500454650269c6100c96610068861004826100c5c61009c0390096039004c03500eb035012c02d006f029024e029013c82901ec22901dc029010a829006a42901ea22901e922909288290067029021682901e622901e58290125229012382900bc825006c025002b02500ea8250128825009382500624250368819015501500338150063015006d00d005c00d006b00d019820d00c340d01e8f120128e8e0308e8a0124e8a0122e5a0124e560188e5202a4e520128e4e024ce4a0188e4a042ce46066ce2a066ae2a0428e2a0666e2a0424e2a0422e2a01e1e2a0066e1e00c4e1600c2e16)) (M 12 0x42c171016d55100cc15100cc541024a50500f92e90758ce90179cc106c8cc100396a90398ca9006b4a5012a0a50239ca10248aa100c88a103182a10188c9900c8899008a09501c9095006d471012d07100692690368c69018886503c98610368c61012886100c5c6100c586101ec055006a055042d04500cc04501e884500be0390196039024b035024b02d00cf029048e029025d229010c829028c42903cc229012a42903ca229027922905f8c29054702903c682903c642906c6229030582902452290243829024322902cc825008c42500cb02501aa825006a4250248825024a0190185015001e00d024c00d02f820d03c8f1a0248e8e0548e8a0304e8a0242e5a0488e5203c4e520248e4e06cce4a0188e4a018ce460ccce2a0ccae2a0848e2a0cc6e2a0844e2a0842e2a03c1e2a00cce1e0486e1a048ee1600c4e160182e0e)) (M 2 0xcdce1005d8c901096c100492c100592b100190a500192a10069099005b49100eb09100a94910079091006908d0059079006dc690068a6100288610065c6100252610064a610024861006544d002c0490039c490095c490064849002984500688450055845002544500648450013845006c039003d035003c035005a02d002f02900ce02900ac82900ac229003c02900aa82900aa229007a0290089829002882901682290027029003682900a622900752290154829009382900532290022829003a425006882500768250064825002e019004d019004c419002c019006a419007d015006c0150053215006c40d006a00d005640d001340d0012f4a0032f420068f1a0028f1200eae920168e9200a4e920162e92014ae8a0068e5a0068e560068e5200a2e52022ce2a022ae2a0168e2a0226e2a0164e2a0162e2a00a1e2a0028e1e00400730020053))) (C 21 (C 72 (C 10 (C 50 (M 4 0x1c159010c351004c151014c94900cc145003cd41004c541004c331004c131008a331004a131004c129004a129004c125004a12500cc11500fc51100c951100cf10d001e10d01cd10d00bc10d01cb10d00ca10d00c930d001c50501c86e101482d100c86c501786c100382b1008a0a100886a10148271011886900c8c6100886610045851010545100c4c510094a510033451004544d007444d00b58490214449008e22500fe02500ce01900da01900258190093019003621500750150192215005620d00c520d00c320d02c1f1e0408f0e0446f0e0445f0e02c4f0e0443f0e02c2f0e01d1ec20082ea601d1ea20032e9601d2e9200f1e9200c4e8e0044e8a0084e660171e6200c4e5a0012e4e0132e4600c6e3a00b6e360011e3600c1e2e0152e260044e1e0071e0e) (M 60 0x2fa12903a95190b4a3110b4a10d0b4950501df0d103c86c503c70c50b464c512c92c101d8ac11c386c1025a0a510764a503fa8a10a5a4a100ca2a121c86a10b4a0990b4a09506ca29103ca09104d8c910b4829100a70910a564910b4b08d03ca0890b486890105889024a065108886503aa8610618a6121c8661018826103c646100f64590a53859148d051048c451087a45100e9451032585104dc84900db04912c984902d8c490dfc84503cc0450b46845063584503c48350b4e02d03cc0250b2a8250368a2505b682511564250d3e019067c0190e2b01905cd01515e7015062221501ff00d01de00d0b4540d0e41f8a12c1f863fc1f5e2941f1e0d85f123c08f0e2944f0e6902f0e1145f063fc8eca2942eca3fc1eca0881eb20781eaa1941e8a0871e7212c1e6a03c2e520b42e4e0e11e4a0b41e3a0781e3603c2e1e12c4e0e)) (M 30 0x85c149053c54105ac10d05aa10d00a86e90d286e109192c910e86c101e82c101e86a50c49ca101e98a104696a10048aa1006b499054a09907382710235471024c06d017986903c5869032d465064c0650548c610568a6101e8861028866101e826101e52610068c490234849028464906ed0450148845073544501ee03902fc43900da039015d035045b03503fb02d011a42d005922d005642d01ef0290b4e029050d02901bc829096c229096a829096a229024a02906198290be882909b822909668290966229028602905a582905a522905a282903c222907bc825014c42501ec02505a882504334250bae419054a01905a501505a3015032600d0968f0e05a8e961272e92032ae8e05aae8a0f08e8a05a8e5a0f08e5205ace4e0face4a01a2e461fece2a1feae2a14a8e2a1fe6e2a14a4e2a14a2e2a0961e2a01eee1e05a2e160236e0e0964e0e0222e0e)) (M 24 0x30c561018d545044d145044d34101cc741018c541018c341060b33105cc925014a925034cb21018c921030c52105cc32108cc121018ad21004a921018a521060a12104891190409115004c311060a51101ca3110089311018f10d0a8e10d0d8d10d064c10d0d8b10d048a10d16c910d02ca90500888e101486e107890d107890c9004c8c5034a8c501898c502090c50088ac512496c101486c107894b1048909904890950788291014907106482710788869078906504890590185245048484504844450432845018d03903030390483035048522d04848250482425048c019048541901830190c52815013221508c700d1983f1e1082f1e3188f0e1986f0e1985f0e1084f0e1081f0e0302eaa0181ea60ce2ea206a1ea20482e8e0604e8a0602e8a09a4e620031e620484e4e0184e4a0062e4a0971e4a0864e2a0781e2a06e2e260184e1e0302e1a0422e0e00a000f)) (W 0x5a0a5005a4a10038295006ba910059291003868d002b089005a8890029889001948900464710016071001686900160690018665001826500160650038c61001886100886610036059001f055007d055009c055005b055005a25500a9055007705500360550023255004c451001c0510039451003e04d004c249001c0490039849001944900258490038645003544500334450013039002283900268350012a35001c229003882900268290056229002e025004c825001c42500386250016425001c819002c019003a019003581900390150035015002e00d003600d0025f1e00b1f1e0035f160065f120128f0e00b4f0e0065f060021eaa0051ea20034e9a0011e8a011ce560119e5600b8e560115e5600b4e560052e5600b1e560034e2e0011e1e0021e160024e0e0021e0e001002f))) (C 5 (C 84 (C 37 (C 70 (C 6 (C 80 (C 56 (M 2 0x360a1004c879002d0750029271002d865007606101350610069055004504d002444d002d049002c04900898490029249004584900452490046845006584500a54450024445006c039004d8350026835002f03100ce03100ac43100ac231008c031002b03100aa43100aa2310049431006923100a643100a6231002603100652310064c31004343100832310062c31006b02d002e029002c829002c029002b0290029829004682900260290064629004c825002c025002b02500694250026025006342500ad00d006c00d002b00d0064f1600e6f120082f120064f0e00a8f060026f0600a4f0600a2ec200a4e9200c2e92012ae8a00e8e520082e52022ce32022ae320168e320226e320164e320162e3200a1e320022e1e) (M 2 0x394f100798e500a90e50069ce10029ae100794e100890b900abab1006908d00a8269001d8650029065001886500e9a6100686610039855006304d007d049002c849002b84900878490036849002604500b504500348450064445006b0390067835002f03100ce031003d03100ac43100ac231004b03100aa43100aa23100a92310068a310068231013703100a643100c623100a54310065231004443100632310062c31004c02d002b02d002d029002b02900c882900270290045229002e025002d025008c82500870250024425012700d0034f820132f820098f120018f060052f060078ed20028ec20162ec20064e9a0138e92006ae8a0044e8a0032e5600f8e520072e52022ce32022ae320168e320226e320164e320162e3200a1e32002ae1e)) (M 24 0x6082f103082e1018a0d100782d101882c101e82b1078a0a500d586901850690175865001546501850650239c610309a610488a6104886610555c61048a059048a055108a05100a904d03e504d0486849088d8450386045048444500bc03903da03901fc035018a0350115035018f031090e0310a0d031078c431078c231078a431048a231018a03106b94310789231078703107764310b0623105554310484c3104834310483231048a02d018e029055c829018c029030a229018a02903b8229023c825018c025018a02500d9425011682500164250375825022542503d2425008d00d048c00d00eb00d048a00d026500d00b340d0034f821984f421082f420758f120e82ec20758e920484e8e0908e8a0304e8a00b4e4a0782e4a198ce32198ae321088e321986e321084e321082e320781e320038e1e0156e1e0930067)) (M 6 0x294a900290a5003928d0048a5500e4855006c051022a05100c925100e825100b904d007524d006c849006c04900f92490128249006544900f4649006c04501c9445006904500c82450045a450025845004544500448450126835006cc3101ec43101ec231006c03100ca43102aa231006a031012823100c6c31006683101e623101652310123231005822d00d602d004c029006a4290048629006322901e64250066025012442500c3425006f01902ae019012d019018c81902ab01900ca419006a0190129019042881902a70190066819018601901254190123419018d00d012c00d009900d003600d066ee1a066de1a042ce1a066be1a042ae1a0429e1a01e8e1a0667e1a0426e1a0425e1a01e4e1a0423e1a01e2e1a01e1e1a020007702e0037)) (M 120 0x168c119168a119073a11543da111168c9056fa8cf12588cd1017c8c110694c11e08cc12ef8ca111486a1149989900e527509792711c18c7100ec8691c1926910a986515cc06103e86610975c612585861078546103f90550f58251168824d07890451164845168464501fb0391497039114d035054c835348e031078d031258c231078b031258a431258a2311688c3116382311ff7031258643142a623131b60311e05431168523101f4c3106f3231051243110722310ccd02d016862d086502d1d4f029078d029078b0290e252290df3229078d025078c825258c425152942508934251173019168c00d239b00d1012f825282f1a0f56f162838e922a58e8a1e04e8a1682e5a0f54e560342e564334e524d7ce4a12bce467f8ce327f8ae325288e327f86e325284e325282e322581e320784e1e1c18e1a0bc2e1a0978e0e0eb00670a30037)) (M 8 0x4c0d100c90d10019899017609900cf895008f09502bb895038b095035a09500b9a95027989500e929500c8a9500c889502678950186095018908d0289471028827100a5a7101a926900858690065069001d865018d065028546501888450188645018444500e3045008783901060390186835038e031028c831028c431008c231020a431020a231033a0310188c3100c8a310178231036703102864310224a31018443100d30310182a310252831018c22d01fd829008d029008822900270290206229008c225008a425008a2250086225012442500b30250182425018c01900160190183019018d00d018c00d010900d006500d0118f06088ae960468e960284e960582e960128e8a0188e5a00f8e520188e4e0198e4a0202e4a088ce32088ae320588e320886e320584e320582e320281e320082e1e0178e1a0340067024005f0040053002000f)) (M 8 0x2dc171063dd51018a949018c11900fb10d02092f101e82f101982e1016a2d1008a8c1012a2b1028a8a500bb8a10319ca10209aa100892a1015b8990036099016a895010908d048a889006988900182710105c7100a4471023e069004d069001986900ea86500986610084661009904d00f704d037b84900678490087049018a84502078450087045024d83900ba03500d383502cd031028c431028c23108ca831010a43102894310188a31020823101268310286431028623105a603102854310024a3100b323100ab02d00ea02d011e029008d029028c829008b02900f3229008f025004e025008b02502ea82501658250219819018301900c181900fb00d018a00d018900d009300d0204f820884f520582f520258f120388e920204e920184e5a0182e560254e520134e4a0084e460102e46088ce32088ae320588e320886e320584e320582e320281e320084e1e0038e1a00300770330063)) (M 12 0x1488d903c9ac501390b900b90a902f82a902486a101c82a1006b29501e8895019b291018aa9100ca8910248a91019908d030a88903ca28900ca0890019489024d87103c886900cc86500cda61001ca61030c86103cc26100c946100f9859024d855010d251024904d0095849002544903c5249023484900b4649009984502d944502b904500b4445024c03901dca35007c035035c431054c031021a43100ca0310248c310326a31027643100c60310244c310152c3100f2431023822d001602d03c682900a602900f5829024322900faa2501ba4250019425015642500c6025007c41901dc019024a0190156019004501900cf015054e015054d015054b01504ba015024981503c921503a701505660150245815018381500c3215015a00d01a700d00e600d024500d0ccee160ccde16084ce160ccbe16084ae160849e1603c8e160cc7e160846e160845e1603c4e160843e1603c2e1603c1e160160027017002300b0003))) (C 19 (C 88 (C 5 (C 40 (C 84 (C 74 (M 5 0x1c949007c34900aa539003c331007a531002c525006c11900fe11500aa31102da111009e10d006d10d005f109005e109013d309005d109009c90900fc30900fa30901293090419109018d10500fc90500f99050058ce101e84e101984d101984c501984b100384a500f9c99006e095005929500f968d01984710038c690198465005846100fc055013c451005c05100e84510018251004c445005c04500f843900fc035019843100f523100f4431037842900c84250196425007342500b282500f600d008300d016240d0556f1e0553f1e0372f1e0371f1e1318f0a0555f0a0374f0a01a2ec20192eaa0071ea60044e960112e920211e920104e8a00f4e6a0341e6200f2e5a0092e4a02d5e460012e4600f4e2e0054e1e00c6e1a0033e1a0191e1a013006f005003f) (M 8 0x20c949006c12d020c729020a729008a52901cc12500cd11500c931500ae511008e111046a111016e309012e109014d309008d109028c309028a309008f10501ee105008c90500a990501e950501e98e101886e100282e102894d100a94c501e84c503894c10188cc102884b1010a0a500e84a5010c09502094910188491010848d01ad07100ec4710288465002a061066906100ad05900e9459018c055006c45103a94510188451014c4450108445016c0350029035008c031008a0310188431008602d003442d001342d00860290172229008a0250286425008602500b5425009520d03f240d0288f0a0886f0a0885f0a0584f0a0883f0a0582f0a0581f0a01d2eaa0184e9a0084e960202e920084e8e0551e8a0274e6a0194e4a01d4e460034e3a0151e3a0306e3200b1e2e0392e2a0156e260081e1e0016e1a01f3e1a0282e1a)) (M 4 0x7cd79024c159002c155014c351004c151011c529010a729003c525004a925033a12100c9519002e11500ac115022d511003d111007951100ce10d004f10900ce30900ee109015d109013c909051a909014a309014990900c930900ae505004d10500ea905004a8e101884e100284c501b9cc101082c1014a8b1014a8a901484a500ca895002949100c848d014a8650088465004846100c484900c384900c644500c484500838450083045004244500ca835021ac31004a83100ca42d00aa829022842901468250046425004622500c44250042825008a40d00c300d010240d0446f1e0445f1e0443f1e02c2f1e02c1f1e1388f0a02c4f0a0041eca00e2ec60091ec200c1e9a0121e920144e8a00c3e8a0144e6a01c1e6200c4e5a00c5e5600b5e520142e520091e5200c1e3a0072e320041e1e0126e1a00e5e1a0041e1a)) (M 5 0xdd389005a12903ca121009c115003c51101ee10901cd90900cc909005e105018d905009c5050118505003dce1008c8e102d84d1019d2c901984c5005c8c1014d4b100970a900570a500558a500f54a5019c2a1019a8a1019a4a1019a2a100a98a101992a10068aa102f88a102086a106584a100668a100f5099005c09500a5095002f49101a6091005f08d006848d004748d002c07102d847100ed26900bc069019846500ad261005886100f505900f5055037d45100f8c49015d445013944500f844500fc03500fe43100f8431016303100ae42d011c02500f982500f842500f601900a700d00f600d014240d01b3f1e0371f1e06b8f0a0556f0a0374f0a0372f0a0032ec20558ea20552ea20371ea201b2e920194e8a0192e8a01c8e620142e4a00fae3a0031e320052e2e0322e2a008ae260052e1e008be1a0161e1a005005b)) (M 10 0x7c2c9009d4c500d84c500d8cc100a88c1015a0b502aa0b100884b100a88a101686a101384a100aa89900c9099011a89502ca491029949101e908d017a889014a28900aa089008928900e888901e82890148471018886901a82690328465039a0610118c6101c8a61008866100a846100a8261013905900b505901e90550099451020925100a905101e845100a5a5100a54510084c510305249003c845032c44500ac24501e8445005444501ec039014ca3500a603500a683101d643100c543101e243101ec22d028682901c622900a60290025229012482900c222900ac025006a42501e842500e642500a60250122425010c01901e9819016601900af015046e015046d01502fc815003c21501ea215014981500a9215046701501e601503d501501e3815019600d01c540d00e240d0aaee160aade1606ece160aabe1606eae1606e9e160328e160aa7e1606e6e1606e5e160324e1606e3e160322e160321e1600700670160027017000b)) (C 120 (M 5 0x23e161019c361041c161006d559023d141005cd41005c94100fb11900fb11501cb11100aa31100b931102ab10d00f910d014c909017b909030b109015a90900fa30900f9909005b105004a905004990502a8505012b0e1011a0e102884d100698c900794c900c84c901984c501db0c102490c1014b0b100590b100b94a900e92a901984a5041b0a100fb09900fb095028b49100fb09100f848d01cb08901b8489003e471007947100f3869007c465003b46500bb055004e44500fb03502dc43100f3229004b01502d220d0192f4a0374f1e0508f0a0556f0a0365f0a0553f0a01e2f0a00a4e6a0074e620371e6200f2e5a0042e560314e520062e520345e4a0064e4600f1e3a004ce3200f6e2e01f8e2a01bce260138e2600a1e260059e1e00e5e1a0194e1a0295e160030057006003b) (C 17 (C 48 (M 6 0xcc15900cc94900cc139017c32901df525014a721012d119012b115042f511012f10d0b4f109024e109012d109012c909007c309024b10901ea90901ea30901e9909001930900cf10501be505006e10500cd505008a505003a0d101a84d100670c900168c900c84c501264c5018a0a500690a5012c09500aa08d008908d0188471006707102bf465006d065006a065011f059001c059012b05502af051003e451003c051012b4510125835018c431006c03100cb431006a031012543100bc02d007942d005642500c5425006442501234250193025007f01901d70190123019012b015012a015012901500bc00d022b00d009900d0061f8a01e8f0a0666f0a0605f0a0424f0a0663f0a0422f0a0421f0a00c2eb20082ea20421ea20084e9a00a2e9a0164e9202c3e920382e8a00c1e6a0181e620182e4a01e1e4a0126e3a0146e2a01e1e2a0062e1e004005b00c0057) (M 60 0x4ad38905bc94903cd11103cb111097a50d10de9091ede3090b4d1090b4c9090b4c3096dab1090b4a909078d50521cb50506488e107884e106470d9384b4d1014b0d102874d10c878c906470c901dc8c5085c0c5078b0c5012a4c5078c2c112ca2c112c98c112c94c112c92c10b48cc114b8ac114988c101d86c138484c112c84b108690a506f88a503684a506f50990a6d09500e9095294609103cb08d078908d028a47110460710f0e46503c60650b4e0550c860390b460350e2c4310feb4310b484310b4602d258e42503cb02500ed0190f6b01911860190f0b015078a8150b4601501da00d0b4900d0b4600d097540d12c8f0a3fc5f0a2944f0a2942f0a2941f0a3fc8ec22942ec23fc1ec20951eaa1ba1ea20451e9a0f04e8a0598e6a0d31e6a1c11e620b49e5a1689e5212c2e520889e4a100ae2a12c1e2a03c4e1e0e300771a4006f0680057)) (M 8 0x1ad149018d10d04af30902e84e5020a6c1014928d004848d01eb089008a08900890890168c8901482890028471004687100a62710106269010aa650108865020846500c686500864650044861018e059015e255003d05500bc251008b051018845100a52510184c51082f04501de045028c845028c445008b045028a845028984502894450388445036704501868450186445028584502854450183845018344502c30450582445018c229008a0290028c29016882900860290185229003d025005c2250188a25018842500864250184825046b0190027019048f015048220d0141f260288f0a0885f0a0584f0a0441f060061ea60061ea20184e960084e92088ce460889e460588e460885e460584e460282e460581e460181e3a0084e360101e3602c4e320184e2e0084e1e0360077008007302a0067002005f)))) (M 360 0x23fc16d168c1452d0a539168c129438950d708990987084e170884d12f388c933890c53d088c516894c12028ac116884c170884b1708a6a970884a5091a6a14388ca12368aa1438b09917db0952bba0952bb929143884911b08291438848d2aaa88944d92895a0847116844712d048692bb4865708c8612ecc261168a861010a261168846112864614383459423b055015325541cc251168c051438845114482512ed6451168f04d625e04d9d8d04d683c44dee7904dbd1844d168704d438604db40504d438324d14b48492f48845082c4390e6c0392d06039438c035168c031438a431590a23116860312e04431153c02d2e5442d04060293b3e025168c0252f6a825158a025438882508560251534425288c015438601542330157e91f9efff1f9ef781f1e6818f0afff8f0a7624f0afff4f0afff4f0a7e9ce4efffce4e7e99e4efff9e4ef788e4e7e95e4efff5e4ef784e4e7082e4ef781e4e80f4e2a7081e2a1684e1e7695e1a3b74e1a1c54e160244e0e009007702000571890043c84001b))) (C 3 (C 24 (C 25 (C 5 (C 21 (C 73 (C 56 (C 9 (M 120 0x168a119168a31110fa10d059910d059a30950991050b1c2d1015c8c910562b107862a561860a1034c099134a099078f0950f0a095078e091153d491078d29103fa2911296491168549101552910d1d28d097c28d1e0e289078e089187d089044908903f688904e62890785289258e0851c1d0850c6c8850d1c485348b085258a885258a485258988525894850a28885168688511a648515358850f0548525842712584269168c059187c451153524d168c039168c035078c031059a22d073902d09d842d17dc82910fc229168882908d62290a72229134c01917d1f423911f1e1682f161b68f124338f0a01f2f067f8ae867f89e865288e862584e867f83e865282e865281e863a18e520151e4e2d09e4a2582e4a01a9e464671e46391ae3211f8e320789e1e0ac3e1a2581e1a) (W 0x1e0850038a850034471001626900160690015051001485100344510034251003844d0019449003884900284490036039003c035001c231001c031004b231001a03100184310037231003602d004c229002b2290028c290034829001f025006e025001d025005c825005c425007b025005a825007a42500d90250038825003862500b82250066825005642500462250064825003462500238250033425001282500b2225006d019003c0190052f460062f420018f1a0048f12011ae8600b8e860054e8600b2e860032e5a0012e52011ce26011ae2600b8e260116e2600b4e2600b2e260051e260012e1e0010073005006f)) (M 4 0x4a321004a1150189105014c8e5014c4e5012cae1019c6e100888e100c86e1002e4c501498c101394c1016e0b5005c0ad00170a900268a90088aa500784a5004caa100c8ca100188a10066aa100864a1002609900a509900cd295010e291004a09101070910085091006e08d003b08d003908d001f089008e289004d08901f7289003f085010d085019b085014a885014a48501ca08500194850238885025848500d7885005748504b7085012688500c648501c58850115485008705900ca04d008d049006c04900ac039002503900cc035003c031012623100160310055231014c229010a229004a02900c242501a701900a60190151f220148f06044ae860449e8602c8e860144e860443e8602c2e8602c1e860141e720148e6a0042e5a0209e5200c2e520121e4a02c8e4600b8e320062e3200cae2e004ae2a00c8e260141e260042e1e)) (M 140 0x6cd37108ca1250c3a1150e1a3115239311167a10d03da3091a4930944992f10cf92c537f9ac114f98c111884b108c84a908c60a903d86a511868a51a48ca111866a11a450991a4929504fe29108cd091118c4911db92912367091092e08d112708d08ce08908cc88915bb08919ea2891f3928908cf0851a4c8851a4c485279b0852bca8852bca4853daa08516d98852bc9485328908508c70851a468852bc64851a458851a45485155927116752712bc42691a4c0591e1c25108cc0510f8905116450511a4d24d08cd24908cc8494ec92491a4c03908660351e7623113b6031006622d2ffe229279e02908ca02918a222503de01908cd0191a490193fd2f266041f2646f3f1e0e13f1627f8f0a4ac8f0694cae8694c9e866048e862bc4e8694c3e866042e866041e8613b8e521be8e462bc2e4611e1e362e22e3219e1e2e3222e2608cae1e27fae1a158004f)) (M 8 0xba289008a08900e8c89008708900f588900a5289018c485038ba85035b085028a485008a085028988502894850089085018888500870850186485018588500e54850104471003e069005886901886690088469001585900f54590084859008f055038d055006c855013c25502fc055003b055007a05501d9255060905501182550286255019525502f50550183855018504d022c849015c24900b924900a8c490055249018844500b54450182839032e031008a03101684310086031008a02d010602d008c429028a82901da22900288290018229003e025008c425008a025010642503522250287019010601900950190188f160221f0a0108f060361f060188ea20709e860588e860284e860581e86088ce560889e560588e560885e560584e560282e560581e560181e360081e2a0081e1e0390073007003f)) (M 20 0x6490c5028dac103798c103c8cc101284c10329295014a08d020a889002a48903ea28902d9889032928901490890098889076aa85062a485014a0850649485014908503c848500fc871019847103c345900aca5500a90550285055014c051014905103c84510056451014585104054510184c51014604d00f544d005504d0505849050524901450490284649014904501f864501d84450155445014524503ca03901ec83501ea835014c831064c43101c843102464310244c3103c502d023c82901ec229026a829014a029016882901f82290184829014262901d862503b6425028342505c2225058e019033c01900a901901f6819014f015034e01508cd015046c21508cb015026a21508ca01503c901508c701503c601503c501503c3815154ee16154de160dcce16154be160dcae160dc9e160648e161547e160dc6e160dc5e160644e160dc3e160642e160641e160bd0033007002b)) (M 10 0xac0f5001d0d1026c2d100ac0d100ac2b100ac0b101ec09901ed09500af09100eb28900ab08900aa28900aa089028928901a8289050ba85056b685032a885050a48500aa0850329885032948500a908501e88850048485008c075002c271026c07100aa07101fe065027d065032c865032c465018a06501e8a65050886501e866506a8465030646500a606500c5465064486501e466501e3465014c05900a7051026545101e425100a904901e824900a704901e584901e424900ba0390136039014903500a923101e8c31002643101e5231014343100a2c3101e902d027e029028a229001682901e422901e2a25008282501ea01901e601901e501903cb01501ea01503c1f220328f060aaae860aa9e8606e8e860324e8606e2e8606e1e860aa8e660aa4e6606e1e660188e5201e8e4e0388e460322e4600a8e360081e320288e260201e2600a1e1e004006b)) (C 7 (C 11 (C 35 (M 12 0x3ce2d100f90cd018e0b100cf095030d09500cd091016b29102ae085009d085092b8850a5b485018b08503ca48500ea28501ca08503c988503c94850248885024848501878850336485024548505e4885084448500aa271024827100e4271009e06900fd06903c526901b4269015546503cc86103cc46103cc26103ea86103c92610248c610248a6106088610248661060846100964610186261024586100354610244c610464a6100248590223059024c05500ce25100cc05101ab251024a251002a051024904d009e04902482490243249033304902450390244231003323103cb029015a029003c02503314250487019022601900230190246215021301503c8f060ccae860cc9e860848e8603c4e860842e860841e860cc8e620cc4e620841e620118e520172e520738e460248e3605d8e320038e2603c1e260252e16069007700f0047002002b) (M 60 0x30cc0ed03ce0d1082d0d1074e0b10b884b10f0f8a9082f8a503cd0910f09291082649103cf08d12ca28d030a08d03c928d128908d078b08903ca08903c948904c82890326889302b88503cb48510ab08512ca8850c0a48503ca08512c98850b8948503c90850b4888506884850f4e07103894710c748690fcb46512cc86112cc46109ac2610b48c611e78a611e088610b48661174846103c826103c686107b626103c54610b44c610b44a6152846610b4305903f72550753055092c25113c90510aa525106c904d048824d0b44249030324906ca44500348450653445035a03507f6035022b0310b4823103b64310b444310b442310b482290b4462502024250e6d01906670190b1601503f301522f2f4205c8f062221e8e0721e8a3fcae863fc9e862948e8612c4e862942e863fc8e623fc4e622941e620658e4a12c2e4a0b48e3a1e08e2a0d08e1a12c1e1601b005f1c00047)) (M 60 0xdfc2f1130c0f1085c0e9011c2c901968c503cc2b1035c0b106b58a911fb0890dfa28903ca08903c9489203b6850e4b0851e7a88512ca48503ca08512c98850fc928529488850b48485074c07112ca0690c0d2611e0ca610d196612bd90610b48c610b48a610c154610b44c610b44a6124b486103c426105fc059037505503cc8510f0945103092510b48251084525100da24d04c844d0b44649035c84505b86450b484390b4c835007c831040a23103ca0310b482310ad62310b0323103cf02d145e02d0f0d02d12cc42d0f0b42d25eb02d059862d12c822d14f702d067642d0b4422d0b4302d1136829066622904948290b4382903ca0250505825004382505fe0190b4d01905570190b4641909b601506450150e08f0a3fcae862948e8612c4e862942e860558e5a07d8e5605b2e4e1c28e4a3fcce2e3fcae2e2948e2e3fc6e2e2944e2e2942e2e12c1e2e04c8e160d12e1604f007701e00532040047)) (M 3 0x2c2d1003c0d1008e29100d9291009829100ab289001b089006a289003a089002928902db885023b48500db08500fa88500fa48500ba08500e988500f94850098485006c071005c0690096465006346500fc86100fc461008c261001986101b8c6100b8a6102188610188661018846100d82610094c610094a610034861009466100344610034261007c05900160590015059001c055008685500f54510085251008445100142510013451006e04d003904d00e904900482490045249003424900838490066445003f039006d039007b0350029035003c031009a23100ea0310078231009902d003d029005c2290026829005622900958290094229003c025003342500fe01900cd01900a7015006581500352150083015033ee1e033de1e021ce1e033be1e021ae1e0219e1e00f8e1e0337e1e0216e1e0215e1e00f4e1e0213e1e00f2e1e00f1e1e00b007701b0047))) (C 56 (M 72 0x63a12110f84d109090c5040c4b10d88cb103e64b1048c0a9028a0a901ea0a537560a1026e099052649902054990d094913f0b68514ab085288a885048a685168a485048a2851c5988509894850cb92850d88a850115885059c27110f427113e426d128c4690404c690d84a6509d86610d8466102a44610e942610d854590d8425504ac05102d9051120885105b84510d88251033505101b4451072564d0c8c849048c049048904907d884906b484924090450d86439011a0350c74235048c03101ba03105d8831092823101560310d824310d82231037c22d03b862d066262d071e0290a0c8290d88829059682901e60290b848292d2a0250468825002e819089e0190d8c019083d21503fd0150a17215048f00d0d8e00d1b9d00d0d8c20d4cab20d111b00d120a20d09d920d0d8620d14a520d090320d120300d4c8ee0e4c8de0e318ce0e4c8be0e318ae0e3189e0e1688e0e4c87e0e3186e0e3185e0e1684e0e3183e0e1682e0e1681e0e1ae001f1250007) (M 6 0x2a82ed01ac0e5034a0e503688e500e84e5032c0e100a88e100a86e102a84e1004e0c900cc8c9002c4c900670c900668c900c8ac5016c4b1008a4b1006c8a9006c4a90128ca900b6aa50127099011709500ea09100690910056091010a28d00cc88501ea885006a285036988501292850068a85098708501d688500a94710144271004a46901298690029469006a26501898650088661012705900cc2550067055020f051009925101282510067051002924d008e84900c4849012703901142350429031002a22d010262d003882901248290043419024f2150123015018f00d026e00d00cd20d02ad00d012c20d02ab00d012a40d012940d060700d012620d012520d002340d0321e1a066ee0e066de0e042ce0e066be0e042ae0e0429e0e01e8e0e0667e0e0426e0e0425e0e01e4e0e0423e0e01e2e0e0020077004005700b00530230047006001b019001701e0013))))
def cp_8_3 : CertItem := CI (some (BV 0x3600002e00002e00002600002e00002600002600001e00003000002800002800002000002800002000002000001800003000002800002800002000002800002000002000001800002a00002200002200001a00002200001a00001a00001200003000002800002800002000002800002000002000001800002a00002200002200001a00002200001a00001a00001200002a00002200002200001a00002200001a00001a00001200002400001c00001c00001400001c00001400001400000c00003000002800002800002000002800002000002000001800002a00002200002200001a00002200001a00001a00001200002a00002200002200001a00002200001a00001a00001200002400001c00001c00001400001c00001400001400000c00002a00002200002200001a00002200001a00001a00001200002400001c00001c00001400001c00001400001400000c00002400001c00001c00001400001c00001400001400000c00001e00001600001600000e00001600000e00000e000006 0x1d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d 3840 3712)) 1 0x80000000000000000000000000000000 e0 (C 4 (C 70 (C 21 (C 35 (C 11 (C 38 (C 5 (C 1 (C 12 (C 8 (C 74 (C 9 (C 72 (C 16 (C 2 (C 32 (C 64 (C 24 (W 0x399250022229002441900238190033419002420d003320d002140d0041fa20031f920031f8a0031f860052f820061f820051f620031f520031f4a0031f4600b2f420011f160091f120011f0e0074f0a0022f0a0078f060021f060051ee20031ed20032eca0032ec60048ec20072ec20031eb20031eaa0031ea600b2ea20011e960064e920031e920068e8a0014e8a007ae860011e720011e5a002ce520072e520011e4e001ce4a0059e4a0031e4a0071e460011e3a0011e360051e2a) (W 0x33249002344500728450014229003382900544190023019002b00d005700d0032f4a0032f460044f420072f420034f320034f260014f160054f120041f120014f0e0091f0a0078f060024f060032ed20032eca0032ec600b8ec20031eb20031eaa0038ea60088ea20031ea20014e960029e920018e920064e920041e8a001ae860038e860042e860011e6a0138e620134e6200c1e620012e5a0022e520012e4e003ce4a0032e4a0011e3a0011e360051e2a)) (M 2 0x2486100644610054261008445100a4251004524900342490013249008884500a844501280290044819008b00d006920d00e8f020266f020265f0201a4f020263f0201a2f0201a1f0200a1ee20061ed20062eca0062ec600e2ec20081ec20061eb20062eaa0021ea60082ea200e1ea20024e9600c4e920041e8a0061e720061e6a0051e660091e620022e5a0022e4e00a2e4a0021e3a0021e3600a1e1a)) (M 2 0x15485006a881006a481006a281006988100692810028a810028681006686100652610024a6100644610074251001404d00948490094249005584500554450034845007482900e401900e400d0101f420121f1200a2f0a0081f0a0023f060102f0600e8f020143f02026ae820269e8201a8e8200e4e820263e8201a2e8201a1e820061e720061e6a0061e660021e620022e5a00b2e520012e4e0061e460021e3a0021e3600a1e2a)) (W 0x6140d003e009003d009003c809003c209003b009003a809003a209003980900392090098809003700900368090036209003580900352090094809009420900338090033209013ee0a013de0a00dce0a013be0a00dae0a00d9e0a0078e0a0137e0a00d6e0a00d5e0a0074e0a00d3e0a0072e0a0071e0a)) (M 2 0x14869002a8650046465001a261006846100168610027059004a25100a845100270510026451002604d008d049001a24900368490066249004a845005a445002844500268450053845002d041006c841006c441006c241006984100592410028a4100286410035841006544100652410024a410074229001382900560190093019002600d002400d005340d005300d0019209012880900b42090121f0600e8f0200c4f020081f020031eb20038ea20131ea20039e9200e4e9200e8e8a0041e8a0209e82026ce420269e4201a8e420265e4201a4e4200e2e4201a1e420021e3a0021e3600a1e2a)) (M 2 0x6d151004d141006c941006c541006c34100ae131006c131006c125006a521006a32100a9115002f111006b11100a9111002910d012910900290c500690a900290950065049006384900632490066845006644500528450065841006524100442290042829004b01900a901900a400d004300d01e900900a4f820264f220262f2201a1f220122f0600e8f0200c6f020082f0200a1ee20042ec60088ec200e2ec20102ea20048e9200e4e92006ae8a00c8e8a00e1e8600cae8200c1e820061e6a0121e620022e5a0092e520022e4e0012e4600c5e420084e420021e420021e3a0021e3600a1e2a)) (M 2 0x10884100a84410054841002503900ae025006c825006c425006c025016a825010a425006a02500698250028a2500288250028625008842500b682500664250066025006582500654250024a250024825004442500638250063425004282500424250121425004501900a301900e120d01e120900e8f0200e2ec200b2e9200d4e8a011ae86008ae8201a8e820022e5a004ce5200a2e520022e4e00e8e4a006ce4600c8e46003ce42026ce26026ae2601a8e260266e2601a4e2601a2e2600e1e26)) (M 2 0x2c161006c149002d131004c13100ae129006c929006c329006c129006a929004a329006a129002b115001a31100a95110039311002d10d001a3090038909005d105006c505007950500694d1004b0c500290c500894c100694a5002b0910109491006947100a94510069051012944500290350022629001d025006a025004c01900aa019006640d002400d002140d0039209006580900b12090244f2a01a1f2a00c2f2200e8f0a0083f0201a2f0200a1ee200e2ec20061eaa0028ea20141ea20022e960048e8a00e4e8a0128e8601cae820048e820061e6a0068e660068e620101e620021e5a0022e520069e4a00c2e4a00ace420185e420022e3a00e1e2a0047e0e00a6e0a)) (M 3 0xe88e100b82e100590d100998c100984c100982c1016b0a9001a0a9001b0a500494a5004a4a1009a09100d84910059471002527100490690048269001586900fd06500584650023865008906100a506100548610034249002284500c2445003903900c503500992290038229002522900c282900d442500d28250011425003e021009c821009c421009c221009a821005a421009a22100f8a2100386210046821009642100962210034a2100e44210032c2100f262100d2221002c01900c90190075019015100d00d88090085809018420900c2fc20094f820162f820174f420158f0201e2f020062ec201e8e820154e820098e4a0032e4a0214e420122e42039ce22039ae220278e220396e220274e220272e220151e22)) (M 2 0x392710065a6100444510069849006584900650490084045006c84100ac041006844100c8241002d0390026035012e031002d031006c431004c031004b03100ca43100ca231002a03100694310039231004843100682310047031006643100e6231002603100654310024a31004443100e4231006343100632310022c310032231006b029004a829002382900622290088425006702500344250013825002e021006c221006a2210018a2100286210042621006c019008a019001500d00d100d006d009002a8090066809006520900442090022f8200c4f420014f160124f120088f020024f020192f020122ec2004ae9200e4e920058e8a0022e8a014ae820062e8200e2e520018e46026ce32026ae3201a8e320266e3201a4e3201a2e3200e1e320068e0a)) (M 3 0x33059003504d001504900f48490054049006304900bc04500d98450038645001d241003d041009c04100996410099441006884100384410055a41006484100340390036035002d03100862310096031002403100630310158425006482501ae2210038a21010882100384210034a210124019015400d005880900670090016209006520901b4209018e00500ad005009c805009c405009b00500fa80500ca40500c98050039405009700500f680500e640500b5805009540501b440500f380500f340501b280501b14050030c05039ee06039de06027ce06039be06027ae060279e060158e060397e060276e060275e060154e060273e060152e060151e06)) (W 0x54431004243100360290012c2900424250051425006a02100186210036821003622100360210064019005e015005d015005c01500bb015005a015005901500b70150056015005501500530150092815009221501120150010c15007400d00648090094209002a4050039405003640500354050044405013ee16013de1600dce16013be1600dae1600d9e160078e160137e1600d6e1600d5e160074e1600d3e160072e160071e16)) (M 60 0x7888c103ce0990f0d09912cc09912cb099258a099045909912c70990b4c291009829106fa4810b4a2810b4988108194810b4928103c8a8103c8681081c0710b4c0651684c61067504d0e782490b452490b454450df4845089444503cd04103cc841045c4410339441009584112c4c4103c4a410f0e03112c8231045c829033c02903ca0290b462290b46029009682501164250b4602508148250ce28250b4a821045a4210ab682112c4c21027341905e3015146201512c500d078400d21c4209033c80506fc4050a364050ab5805193440524f1f221a42f121a48f0a0783f0a33f3f020bd1f02474ae9a4749e9a30c8e9a1a44e9a4743e9a30c2e9a30c1e9a0331e7208d1e6a0ce1e6203c9e5a14e2e520819e4a0562e4203c1e3a03c1e3612c1e2217d3e1a168ae0a)) (M 8 0xfd76901880a501884a100782a100992910189091027829100f92710095471004846900b986500d5865007d261008d061008c46100d98610218461008a039003a035005603500bb031018943100b84310198231028e02d00fd02d058c02d01bb02d03da02d020902d028702d030602d00f542d019502d014202d018c829005882900b58290202829018a825007882501434250152825018a2210088a2100886210186821018642101862210084c210084a210082c21038801902050150133015010a00d023600d0050a0d018c209002b00903d88090214209010c405018a40501328050388f020482e8a0278e8602cae820418e8201b4e820082e4e028ce4a0204e4a0488e46044ce420302e42098ce2e098ae2e0688e2e0986e2e0684e2e0682e2e0381e2e020ae0601d4e06)) (M 120 0x163d2c107890c108f88c1012c4b10d388a5078d095156c491078d08d528c08d528a08d4b0908d258708d0f58889163d0851e08885168a481168a2811689881168948116892810788a8110d447105b4271168466916848652d0c661005d051168545109552512364451168504517a48450d9c841078864115658410224c4132646410786035168c2311346431102623109a42311e8e029082c829066622916860292588425156682503464250562625168a82101268210ce66210564c2125846210782c21070e0190d6841920250190de60151be501505630150f0b00d202300d0560a0d00dc809168b00510a8f0a23e8f061fa2f062052f025f31f02870ae8e8e89e8e6188e8e3484e8e8e83e8e6182e8e6181e8e078ae820228e4e4381e4a1561e461f78e420121e420782e3a0781e2e1edae2209d1e226fbbe0a0259e063482e062331e06)) (M 12 0xea0d5024a07500e60710246065076c05503cb05503ca0550189255084505504a42550603055016d0510249451025845100d705100c304d00ee04900ec049017a849024a2490079049003684900a52490189045017844500554450134445024344500cd041024c841007c441024c241017984100c9241009584101f544100c4c4100c4641009a039003603900ca035026e031007a431002643103c443100c202d0216829024622900560290224229005882503084250226425015482501dc42100da82101da42100c8a2100c862100c4a2100e2c2100d981902d60190183019002201902b9015007e00d001a00d02f700d01d600d067880901a5209016380900c0a0901ad00501b580503a1f2206c5f060378f020335f020621f020039e9e0574e9201d8e8a0309e8209c1e820e4ce560e49e5609c8e560e45e5609c4e560542e5609c1e560541e2201d8e16012de0a07fce06)) (M 120 0x78d141112c13103fa131082a921168a5210f0e119260c119258b119258a119258911902ca1150179915078c31116893110f0c30906ba309168e105168c905041b50509da9052588ce107d8cd10eb88d114184c53bb8cc11688ca93c08ca105688a111284a1078809502f808d0a780711688c6908a84650de8065008cc611688c6108a82611414261078805507dc0510eb4451078904d041904918f4249117884525848450c94445168c4410788035078802d0fda2290494829168422918a2829049a825197482525824250348a210788621168642102762210784c2104946210782c2116d6019056301902c90150c152151973015022d00d139c00d1eda00d056d00916858090a75209168d00516894050c138050780c058e86f1e8e85f1e1b41f1e6cd8f1afff8f1a6184f1a8e83f1a6182f1a4641f022844e8a4552e823a31e821465e520102e4a1c34e423382e421941e420781e3a2754e321c31e324842e2210d1e1a0c44e164a37e0a2ff7e06)) (C 34 (M 8 0x178091008a88500da08501080850109a8102dc07101bc861008c0610088a6101b4a6104c9055014984901a82490185049014c84500bc0450049845018584500d50450408441008a03901b6035022a4310152031008202d00cb829018a02900e82290166829018c025014a025002682500b602501020250088c2100886210088421020822101260210084c21008462101042210082c210142621002242101a7019010601900850190063019010e015010d01500870150106015018e011018d011018c411028c211024b011028a411018a2110209411038921101870110186411018621101854110285211013421101a3411028321100c900d020500d00c300d0784009004b005010a80500ea40504428050111805098ee12098de12068ce12098be12068ae120689e120388e120987e120686e120685e120384e120683e120382e120381e12) (M 8 0x35a089049908902882890388085016a08103e888101b84810348c610088a610084c610084a61008505902ac055026505503ac84900890490065849018c04500658450165045038444101042410326039008c03501de431008202d01cc8290186029014222900ec025018682500260250204425007e821008e02100bcc21028ca21008862102082210084621008262100da01900f981901070190045019017e0150019015010501500830150080c1501fe011031d411018d011033c411050c211018b011013a411018a211018941101e921102c84110187011028641102862110185411018521101834110183211006d00d006900d028640d004300d010b009008a80901a920900c5809010380902a180900ad005010a805005a405009980500838050482805098ee12098de12068ce12098be12068ae120689e120388e120987e120686e120685e120384e120683e120382e120381e12)))
def cp_8_4 : CertItem := CI (some (BV 0x3800003000003000002800003000002800002800002000003200002a00002a00002200002a00002200002200001a00003200002a00002a00002200002a00002200002200001a00002c00002400002400001c00002400001c00001c00001400003200002a00002a00002200002a00002200002200001a00002c00002400002400001c00002400001c00001c00001400002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00003200002a00002a00002200002a00002200002200001a00002c00002400002400001c00002400001c00001c00001400002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00002c00002400002400001c00002400001c00001c00001400002600001e00001e00001600001e00001600001600000e00002600001e00001e00001600001e00001600001600000e000020000018000018000010000018000010000010000008 0x1d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d00001d 4096 3712)) 0 0x80000000000000000000000000000000 e0 (C 0 (C 8 (C 16 (M 2 0x30a09002e005006d005002c805002c405006b005002a805002a405002240500218050121f420021f320021f2a0021f260121f220082f120061f1200e2f0a00c4f060022f060183f020062f020061ee20021ed20021eca0021ec60121ec20021eb20021eaa0021ea60121ea20082e920061e9200e2e8a0083e860062e8600a9e820128e820023e820024e720021e6a0021e660121e620062e520081e5200c2e4a00ece4600c1e3200ece2a008ce260061e2600a4e1a0078e16005ee1200ade1200b8e120026e0e0084e0e017ee0a) (W 0x5300d0015809001520900142090013809001320900128090012209001180900112090030a090019405001880500184050037005001680500164050015405001480500134050012805001180500b1f020091ea20061e920074e8a0068e860069e820098e82015ce420159e4200f8e420155e4200f4e420092e4200f1e42001ce320048e32007ce2a006ce260051e1a0028e16001de120078e120014e120041e120014e0a)) (M 2 0x22419008301500294110029211002841100282110025411002341100232110021411002121100a300d002c209001a809002a209002980900282090067009001680900258090025209002480900238090021209006e005006d005002c805002c405006b005001a805002a4050048f020012ed20022eca0028ec60122ec20044e920082e9200e4e8a00e8e8600eae820108e8200e8e5200c8e4a00e2e4601ace420048e4202ace2202aae2201e8e2202a6e2201e4e2201e2e220121e220048e1a0042e1a0028e160088e120016e06)) (M 2 0xe2425002a821002a421002a2210026821002642100262210025019008301900a30150028411002821100670110025411002521100244110024211002341100232110022211002141100d500d002c209005b00900298090029209002820900258090024209002380900228090022209006e005006d005002c805002c405001b005002940500218050021405003040502aee0202ade0201ece0202abe0201eae0201e9e020128e0202a7e0201e6e0201e5e020124e0201e3e020122e020121e02))
def cp_8_5 : CertItem := CI none 0 0x80000000000000000000000000000000 e0 (W 0x51f0a0051f060062f020071f020011ee20071ec20071ea20051e920051e8a0052e860013e8200c2e820071e620051e520052e4a0052e460075e420012e420051e420051e32003ae2a0021e2a005ae2600dae220034e1a0034e160068e120054e120038e0e0077e0a0041e0a009ae060028e0600fce02002be02002ae02)
def wVec_12 : Fin 6 → ℕ := ![10,10,10,8,8,8]
def fastW_12 (m : ℕ) : ℕ := cond (bitAt m 0) 10 0 + cond (bitAt m 1) 10 0 + cond (bitAt m 2) 10 0 + cond (bitAt m 3) 8 0 + cond (bitAt m 4) 8 0 + cond (bitAt m 5) 8 0
def cFn_12 (k i : ℕ) : ℕ × ℕ := (fastW_12 i + 2 * k, 33)
def rowZ_12 : ℕ → List ℕ
  | 0 => (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 23 0x831292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowO_12 : ℕ → List ℕ
  | 0 => (unpackBytes 7 0x40383028201810)
  | _ => []
def rowFl_12 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x31292519150d)
  | 1 => (unpackForbs 11 0x3129232200000000312523220000000029252322000000003119151300000000191513120000000029190d0b0000000029190d0a0000000029190b0a00000000290d0b0a00000000190d0b0a0000000025150706)
  | 2 => (unpackForbs 15 0x2111090500000000211109030000000021110503000000002109050300000000110905030000000021110902000000002111050200000000210905020000000011090502000000002111030200000000210903020000000011090302000000002105030200000000110503020000000009050302)
  | _ => []
def rowFbs_12 : ℕ → List (List ℕ)
  | 2 => (rowFl_12 0) ++ (rowFl_12 1)
  | 3 => (rowFl_12 2)
  | _ => []
def cp_12_0 : CertItem := CI none 0x117177f177f7ffe 0x8080808080808000 e0 (W 0)
def cp_12_1 : CertItem := CI none 0x10117011717ff 0x8000000000000000 e0 (W 0x42ec60031eb20051eaa0051ea60032e9a0032e960032e8e0051e720051e6a0051e660032e5a0032e560024e4e0031e3a0031e360024e2e)
def cp_12_2 : CertItem := CI (some (BV 0x3a00003000003000002600003000002600002600001c00003200002800002800001e00002800001e00001e00001400003200002800002800001e00002800001e00001e00001400002a00002000002000001600002000001600001600000c00003200002800002800001e00002800001e00001e00001400002a00002000002000001600002000001600001600000c00002a00002000002000001600002000001600001600000c00002200001800001800000e00001800000e00000e000004 0x21000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021 1984 2112)) 0x100010117 0x8000000000000000 (N (N (N (N (fl 0x31292519150d) (fl 0x31191513)) (N (fl 0x29190b0a) e0)) (N (N (fl 0x190d0b0a) (fl 0x31252322)) (N (fl 0x29190d0b) e0))) (N (N (N (fl 0x25150706) (fl 0x29252322)) (N (fl 0x29190d0a) e0)) (N (N (fl 0x290d0b0a) (fl 0x31292322)) (N (fl 0x19151312) e0)))) (C 36 (C 17 (C 9 (C 12 (C 40 (C 48 (C 24 (M 2 0x6345100232510094229004641900a700d002640d006620d0061eaa0061ea60021e9a0021e960021e8e0062e8a0101e8a00d2e860061e720041e660021e5a0021e5600e1e520022e4e0064e4a0102e4a0022e3a0022e360022e2e00d1e2a00e4e1a0096e160044e160051e16) (W 0x33251005422900338290043019003581500252150043015002620d007300d0032eca0012ec60031eaa0011ea60011e9a0011e960011e8e0094e8a0021e8a0061e860111e620012e5a0012e560024e520062e520012e4e00b4e4a0011e3a0011e360011e2e0024e2a0011e2a0051e1a)) (W 0x360a5001609900158950036885001602d00362290056029006601900570150046015007600d0112ec20021eb20031eaa0014e8e00b1e8a0084e860031e720031e6a0031e660061e620012e5a0011e560032e520011e520012e4e0042e4a0011e3a0014e360031e2a0031e1a0021e0e0070023)) (W 0x268a100364a100362a100150990034269003386500358610025461002526100150590015055001504d0014649004424900170390015035001542d001682900152290065019002701500160150065015002700d002600d005500d00a2ec20111ea20012e960094e8a0022e8a0042e860061e620062e520051e520061e4a0091e2a0032e1a)) (M 5 0x170c900f547100f5069003644d00a58490057039005583500f683100f623100a60310054c310054a3101e443100832310052a31005242d009602900f522901142290073229023301901460150195015013700d003500d017300d00b2eca00c2ec20054e8e00b4e8a0184e860054e5a0374e520024e4e0282e4a0554e320552e3202d1e320054e1a0052e1a00e002f007001b)) (M 6 0x1e60ad00c3869012566500c424900628390066035006602d01e702501268250126425012582501254250064a250064625042442502a282502a242502a5019006381900634190125215012620d0030a0d0242ec20062e9a0364e860062e5a0062e560094e520092e520064e4e00c4e4a0664e260662e260361e260216e160212e0e01000170100013004000f02e000b)) (M 6 0x16607501264650064c61006466101844610063059008705501670510106051002425101e504d0125249002384902268450125845012544503050450064a4502a444501038450123445002284501824450062439006603501262310302231006422d0134229008282901822290226019014301901272150274e860664e460362e460661e4600f4e2a0214e260211e2600f4e160151e160365e0e010001f)) (C 24 (M 4 0xc64b100462b100562a900362a1004709900c709100c529101a5091004708d00754850044a71008487100c486900c4865002585900248590044855004424d01a484901458450184845004603900448350122431004422d00c682901c48290042829011602500c482500f4425018600d002500d0040a0d0244e920442e920441e920281e5201a2e320242e1a0201e160023e0e0041e0e007002b0160027) (W 0x6729100364910036291003549100352910036889003588900e486900848650014c610014a610054861005446100b426100130590013055001604d00b304900348450033845005304500130390013035001302d0033019006300d0094e920112e920111e920111e620032e520091e260032e160032e0e0020003009001b00200130060007)))
def cp_12_3 : CertItem := CI (some (BV 0x3c00003200003200002800003200002800002800001e00003400002a00002a00002000002a00002000002000001600003400002a00002a00002000002a00002000002000001600002c00002200002200001800002200001800001800000e00003400002a00002a00002000002a00002000002000001600002c00002200002200001800002200001800001800000e00002c00002200002200001800002200001800001800000e00002400001a00001a00001000001a000010000010000006 0x21000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021 2112 2112)) 1 0x8000000000000000 (N (N (N (N (fl 0x9050302) (fl 0x21110502)) (N (fl 0x21090302) (fl 0x21110503))) (N (N (fl 0x21050302) (fl 0x11090503)) (N (fl 0x11090502) (fl 0x21110905)))) (N (N (N (fl 0x11050302) (fl 0x21110902)) (N (fl 0x21110302) (fl 0x21110903))) (N (N (fl 0x11090302) (fl 0x21090503)) (N (fl 0x21090502) e0)))) (C 4 (C 2 (C 1 (C 8 (C 24 (C 16 (C 32 (W 0x142650013819001341900124190011419005501500122150011215005500d001220d001120d0092ec20011eb20011eaa0011ea60011ea20091e920092e8a0084e860032e520061e520082e4a0014e460061e460064e320032e320081e2a0042e260031e260034e1a) (W 0x14485001406500642290064825003442500950190036015001521500250150014015007600d0011eaa00b4e820132e820121e820011e720011e6a0022e520071e520092e4a0091e460012e320081e320031e2a)) (M 4 0x17504900b4249004684500c4845012444500224450045841005544100452410043229013282901244250112825001182500c5019004381900434190042019004141901460150044815004201500c700d007600d009500d0141e920191e8602c4e8201f1e8204c4e4202c2e4204c1e420231e320091e2a)) (M 2 0x268610026461002626100c486100944610094451009425100370490094249002384900232490037045002584500254450034845002344500224450025241004222900218290076025003482500e30190123015002600d002400d00a300d00d2ec20161ea20164e8200b2e820031e820261e6200e4e420162e4200d4e320031e3200c1e2a0081e26)) (C 24 (W 0x1324900560450014245001344500124450084231006602900348290024425007242500168210016421007622101320210065019001401900158150014015001381500122150011015001540d001520d005500d0062e920072e8a00b4e820062e820092e520134e220132e2200b1e220022e16) (C 34 (C 17 (C 33 (M 3 0x124049002324900328490024841010603100354310035231001323100424310164829005282900970250035825003482500338250033425006282500568210156421003622101230190031019011301500120150031015016300d0112ec20214e820062e8200d4e520154e420212e420394e220392e220211e22) (M 2 0xa4049002384900232490022849002544100c4841007424101042310023431010422900228290057025002482500b282500e682100c6421009622100c30190021019003601500242150073015010300d0202e860164e820062e820032e520022e4a0112e420264e220262e220161e22)) (M 2 0x1624900650490094249012484500d40450023445002284500224450025841002544100960310094231004602900e2229002382501028250026821002642100e62210123019009501500240150021015007500d002400d002320d0010a0d0154e820064e460162e460204e420264e220262e220161e220014e0e)) (M 3 0x1160850034485005446100332510035249009484900542490032849003544501644450023445012484100d444101a443100134310015829002422900338290152829002582501944250156821010642101562210106019003441900230190195015019300d0212e8a0214e820182e820072e4a01a2e420394e220392e220211e22)))) (M 10 0x4466500b4461018305103b50490104249005404900a5245008504502d484501b4445020444103f60350114031005302d001482904a4229022482500644250322a2500a622100c602100e501900a4019006281900a1019023601501d50150063215046300d02a700500a680502f640501b580500a540500a480500e4405022380500f340503c280500a2405049180500f140501e0c050be6e060be5e0606e4e060be3e0606e2e0606e1e0609e0027)) (C 8 (M 3 0xf305100350490124249003544500e504500448450034045005504100648410036431008603100d4431004602900b48290064229006282900b4425007402500624250126019003341900b50150014015003600d012300d00e700900968090066209003580900b5209003480900342090123809003320900328090032209003180900312090090a09002480500328050396e0a0395e0a0214e0a0393e0a0212e0a0211e0a02e0017) (C 16 (M 4 0x1c426100b445100358490115249008424900b303500a60310072431011402500f1825003642100d602102048210152821020222101560190035019004341900d5015005301501c500d01970090046809004620902158090045209004480901938090243209004280900422090041809004120900c0a0900164050045405004440504c6e0a04c5e0a02c4e0a04c3e0a02c2e0a02c1e0a03b0013) (W 0x54445004524100444410034241005603100222310072025001182500464210084821005422100828210012221001641900660190073015001540d006500d00370090016809004620900958090025209001480900142090093809009320900128090012209001180900112090136e0a0135e0a00b4e0a0133e0a00b2e0a00b1e0a0130037011000f)))) (C 2 (C 16 (M 10 0xa4271010586903c426100f504901c4849050404501e2835030603100c483101e243100a422903c2829009682500a602501f482504a44210062421034601900658190087015032301500c0c15016701100a641105a6211054541103b521100a441100a421100a321100a241100a221100a1411028121102e500d006440d012080d0315005001240500a14050be6e120be5e1206e4e120be3e1206e2e1206e1e1206e001f) (C 8 (M 3 0x3404900930490115045005444500c50410054441018424100e443100d243100c602900a48290022c290114825003382500224250022225010601900520190035815004501500e3015015701100b641101b6211003541100352110034411003421100c341100a3211003221100314110031211005600d003400d00a300d003200d0396e120395e120214e120393e120212e120211e120330023) (M 2 0x94849007544100e4241010202900948250072425002682100d60210104421002422101022210076019007501900770150026015005501500c70110026411010621100b541100452110024411002421101234110123211002241100222110021411002121100b300d003080d0266e120265e120164e120263e120162e120161e12026003b022001b))) (C 8 (C 16 (W 0x2404900644450014a310054231002223100268290046029003422900724250024815004301500128150036411007601100154110075011001341100730110011211004500d003080d00370090066809001620900858090025209001480900142090083809002320900128090012209001180900112090136e0a0135e0a00b4e0a0133e0a00b2e0a00b1e0a011000b) (W 0x3384500250410034a4100342410024a3100622310026829002602900542290072025006481500120150016411009601100154110075011001341100a30110011211002500d001300d001200d003080d0057009008680900462090085809002520900148090014209008380900832090012809001180900112090136e0a0135e0a00b4e0a0133e0a00b2e0a00b1e0a01300330110007)) (W 0x3444900624250076021002442100842210052a210022221004301500370110086411008541100752110014211008341100622110011211006500d001440d0077009001680900162090046009001580900252090055009001480900138090033209007300900128090012209001180900112090030a090136e0a0135e0a00b4e0a0133e0a00b2e0a00b1e0a013002f013002b0110003))))
def cp_12_4 : CertItem := CI (some (BV 0x3e00003400003400002a00003400002a00002a00002000003600002c00002c00002200002c00002200002200001800003600002c00002c00002200002c00002200002200001800002e00002400002400001a00002400001a00001a00001000003600002c00002c00002200002c00002200002200001800002e00002400002400001a00002400001a00001a00001000002e00002400002400001a00002400001a00001a00001000002600001c00001c00001200001c000012000012000008 0x21000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021 2240 2112)) 0 0x8000000000000000 e0 (C 2 (C 1 (C 0 (C 8 (W 0x328490013045003284500324450030c15001301100314110031211003400d002080d0072ec20091ea20071e920022e8a0051e8a0072e860094e820052e820071e620011e4a00d2e420041e420042e320031e320042e2a0041e260024e1a0024e160061e12) (W 0x448290044425003142500148210014421001422100424210042221003101900310150020c150033411003321100324110032211002300d003200d0022e8a0052e8600d4e820042e820062e520074e420072e420154e220152e2200d1e220036e12)) (M 3 0x55849009284501048410034441003424100e6031007243100928290092229003202901070250034825002442500d682100d6021007442100942210032821003222100f301900c30150031015004541100652110085011009441100942110092411006400d009200d03f6e0203f5e020274e0203f3e020272e020271e02)) (W 0x64041005203100120290042825003242500860210044a21003462100144210012621002501500330150056211001601100650110031411005300d0097005006600500558050015005007480500644050043805001300500328050042405003180500314050050c050115e0600d4e060153e0600d2e0600d1e060156e020045e02)) (M 4 0x1150410084c410044841025404101044310102829008242901b402500220250044821014462102426210143019024641100e541100634110043011004400d008300d008100d0157009045600901852090125009014480901c4209002300900c280901c220900c18090140a0901d6405004600500150050023005014240500414050445e0a0344e0a0543e0a0342e0a0341e0a0546e020105e02))
def cp_12_5 : CertItem := CI (some (BV 0x4000003600003600002c00003600002c00002c00002200003800002e00002e00002400002e00002400002400001a00003800002e00002e00002400002e00002400002400001a00003000002600002600001c00002600001c00001c00001200003800002e00002e00002400002e00002400002400001a00003000002600002600001c00002600001c00001c00001200003000002600002600001c00002600001c00001c00001200002800001e00001e00001400001e00001400001400000a 0x21000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021000021 2368 2112)) 0 0x8000000000000000 e0 (C 0 (W 0x10a09005180500514050030c050021e920051e8a0051e860042e8200b1e820071e620051e520051e4a0052e460044e4200a2e420011e420052e2600f1e220024e1600d4e120036e0e00c6e0a) (W 0x524110051211003080d005220900518090030a090023005005280500514050176e020175e0200f4e020173e0200f2e0200f1e02))
def cp_12_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x51e620031e520031e4a0031e460022e4200b1e420031e320031e2a0031e260054e220081e220012e1a0012e1600b2e120012e0e00a4e0a0045e060074e060056e020105e02)
def wVec_16 : Fin 5 → ℕ := ![9,9,8,8,8]
def fastW_16 (m : ℕ) : ℕ := cond (bitAt m 0) 9 0 + cond (bitAt m 1) 9 0 + cond (bitAt m 2) 8 0 + cond (bitAt m 3) 8 0 + cond (bitAt m 4) 8 0
def cFn_16 (k i : ℕ) : ℕ × ℕ := (fastW_16 i + 2 * k, 28)
def rowZ_16 : ℕ → List ℕ
  | 0 => (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 16 0x19151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 6 0x110905030201)
  | 3 => [0]
  | _ => []
def rowO_16 : ℕ → List ℕ
  | 0 => (unpackBytes 4 0x201c1810)
  | _ => []
def rowFl_16 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 7 0x1513120000000000190d0b0000000000190d0a00000000000d0b0a0000000000150d070000000000150d0600000000000d0706)
  | 1 => (unpackForbs 10 0x110905000000000011090300000000001105030000000000090503000000000011090200000000001105020000000000090502000000000011030200000000000903020000000000050302)
  | _ => []
def rowFbs_16 : ℕ → List (List ℕ)
  | 2 => (rowFl_16 0)
  | 3 => (rowFl_16 1)
  | _ => []
def cp_16_0 : CertItem := CI none 0x177f7ffe 0x88808000 e0 (W 0)
def cp_16_1 : CertItem := CI none 0x117177f 0x80000000 e0 (W 0)
def cp_16_2 : CertItem := CI (some (BV 0x2e00002500002500001c00002600001d00001d00001400002600001d00001d00001400001e00001500001500000c00002600001d00001d00001400001e00001500001500000c00001e00001500001500000c00001600000d00000d000004 0x1c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c 800 896)) 0x10117 0x80000000 (N (N (N (fl 0xd0706) (fl 0x190d0a)) (N (fl 0x150d07) (fl 0x151312))) (N (N (fl 0x150d06) (fl 0x190d0b)) (N (fl 0xd0b0a) e0))) (C 12 (M 2 0x23049002284900230450022845004244500214190033015004120d0040a0d00936620062e5200c1e2a00a36260042e1a0081e1a0072e16001360e0032e0e006001b) (W 0x424310042e52003364a007364600a1e320062e0e00400170040013003000f002000b00200070050003))
def cp_16_3 : CertItem := CI (some (BV 0x3000002700002700001e00002800001f00001f00001600002800001f00001f00001600002000001700001700000e00002800001f00001f00001600002000001700001700000e00002000001700001700000e00001800000f00000f000006 0x1c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c 864 896)) 1 0x80000000 (N (N (N (N (fl 0x50302) (fl 0x110903)) (N (fl 0x110502) e0)) (N (N (fl 0x110302) e0) (N (fl 0x90503) e0))) (N (N (N (fl 0x90302) (fl 0x110905)) (N (fl 0x110902) e0)) (N (N (fl 0x90502) e0) (N (fl 0x110503) e0)))) (C 1 (C 2 (C 4 (C 8 (W 0x230510040c15004120d0052e4a0052e4600c36420022e420061e320051e2a0011e1a) (W 0x128250041425002282100324210032221002201900310190031015001200d0020a0d00b2e4200c362200c1e220012e0e)) (W 0x524310023019003281900230150032815002301100314110031211004080d0053646002362a0023626002362200c2e1200c1e1200d0027)) (W 0x32829002242900118250053019001300900328090042209003180900412090040a0900c360a00c2e0a00c1e0a0070023007001f007001b)) (C 4 (M 2 0x62825004222500a3015002300500628050082405006180500814050080c0501836060182e060181e0600f001700d000b00d0007) (W 0x31411002120d003300500328050042405003180500214050040c0500c360600c2e0600c1e0600e001300e000f00d0003)))
def cp_16_4 : CertItem := CI (some (BV 0x3200002900002900002000002a00002100002100001800002a00002100002100001800002200001900001900001000002a00002100002100001800002200001900001900001000002200001900001900001000001a000011000011000008 0x1c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c00001c 928 896)) 0 0x80000000 e0 (C 3 (C 2 (C 0 (W 0x430110032411003221100314050030c0500c2e420041e320031e2600936220031e220031e160053606) (W 0x1223100120310032821002242100522210012019002101900430150042015001241100314110031211001280500320050021805005080500e360200e2e0200e1e02)) (W 0x920390022821003242100320190071019003141100230090032209004180900312090030a09007080900b04050082e0a00e1e0a00e36020062e02)) (W 0x2242100322210052015002101500124110031211006200d003100d003080d003300900428090041809001300500314050030c0500408050082e0e00e1e0e00e36020062e02))
def cp_16_5 : CertItem := CI none 0 0x80000000 e0 (W 0x228050012405002180500114050010c050081e220032e120071e120092e0a0022e0601036020022e02)
def cp_16_6 : CertItem := CI none 0 0x80000000 e0 (W 0x71e0a0071e0600c2e020041e02)
def cp_16_7 : CertItem := CI none 0 0x80000000 e0 (W 0x51e0600e1e02)
def wVec_26 : Fin 6 → ℕ := ![6,6,6,6,6,4]
def fastW_26 (m : ℕ) : ℕ := cond (bitAt m 0) 6 0 + cond (bitAt m 1) 6 0 + cond (bitAt m 2) 6 0 + cond (bitAt m 3) 6 0 + cond (bitAt m 4) 6 0 + cond (bitAt m 5) 4 0
def cFn_26 (k i : ℕ) : ℕ × ℕ := (fastW_26 i + 2 * k, 23)
def rowZ_26 : ℕ → List ℕ
  | 0 => (unpackBytes 42 0x2839353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 23 0x831292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowO_26 : ℕ → List ℕ
  | 0 => (unpackBytes 5 0x4030201810)
  | _ => []
def rowFl_26 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x3d3b3a)
  | 1 => (unpackForbs 2 0x2f2c0000000000002e2c)
  | 2 => (unpackForbs 9 0x3533320000000000332b27000000000035272600000000002d27260000000000332b24000000000033272400000000002b272400000000002a26240000000000391b1a)
  | 3 => (unpackForbs 27 0x39352d00000000002d2b27000000000035322600000000002d2a2600000000002726240000000000352d1d000000000039321a0000000000392a1a0000000000322a1a0000000000352717000000000033271700000000000017160000000000001714000000000000161400000000002d2a0e00000000002d260e00000000002a260e00000000001a160e0000000000000f0e00000000002b2a0c00000000002b240c00000000002a240c00000000001b1a0c00000000001b140c00000000001a140c0000000000000f0c0000000000000e0c)
  | 4 => (unpackForbs 60 0x3129250000000000312923000000000031252300000000002925230000000000312922000000000031252200000000002925220000000000312322000000000029232200000000002523220000000000311915000000000031191300000000003115130000000000191513000000000031191200000000003115120000000000191512000000000031131200000000001913120000000000151312000000000029190d000000000025150d000000000029190b000000000023130b0000000000290d0b0000000000190d0b000000000029190a000000000022120a0000000000290d0a0000000000190d0a0000000000290b0a0000000000190b0a00000000000d0b0a000000000025150700000000002313070000000000250d070000000000150d070000000000230b070000000000130b07000000000025150600000000002212060000000000250d060000000000150d060000000000220a060000000000120a060000000000250706000000000015070600000000000d0706000000000023130400000000002212040000000000230b040000000000130b040000000000220a040000000000120a040000000000230704000000000013070400000000000b07040000000000220604000000000012060400000000000a0604)
  | 5 => (unpackForbs 18 0x312919000000000031251500000000003123130000000000312212000000000029250d000000000029230b000000000029220a000000000019120a0000000000252307000000000015130700000000000d0b070000000000252206000000000015120600000000000d0a060000000000232204000000000013120400000000000b0a040000000000070604)
  | 6 => (unpackForbs 20 0x2111090000000000211105000000000021090500000000001109050000000000211103000000000021090300000000001109030000000000210503000000000011050300000000000905030000000000211102000000000021090200000000001109020000000000210502000000000011050200000000000905020000000000210302000000000011030200000000000903020000000000050302)
  | _ => []
def rowFbs_26 : ℕ → List (List ℕ)
  | 0 => (rowFl_26 0) ++ (rowFl_26 1)
  | 1 => (rowFl_26 2) ++ (rowFl_26 3)
  | 2 => (rowFl_26 4) ++ (rowFl_26 5)
  | 3 => (rowFl_26 6)
  | _ => []
def cp_26_0 : CertItem := CI (some (BV 0x2200001c00001c00001600001c00001600001600001000001c00001600001600001000001600001000001000000a00001c00001600001600001000001600001000001000000a00001600001000001000000a00001000000a00000a00000400001e00001800001800001200001800001200001200000c00001800001200001200000c00001200000c00000c00000600001800001200001200000c00001200000c00000c00000600001200000c00000c00000600000c000006000006000000 0x17000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017 1088 1472)) 0x11717ff177f7ffe 0x8000800080808000 (N (N (fl 0x3d3b3a) (fl 0x2f2c)) (N (fl 0x2e2c) e0)) (C 43 (M 3 0x178b900274b900178b500272b50032eda0032ed60032ece0010003) (W 0x174ad00172ad0012eda0012ed60012ece001000b0010007))
def cp_26_1 : CertItem := CI (some (BV 0x2400001e00001e00001800001e00001800001800001200001e00001800001800001200001800001200001200000c00001e00001800001800001200001800001200001200000c00001800001200001200000c00001200000c00000c00000600002000001a00001a00001400001a00001400001400000e00001a00001400001400000e00001400000e00000e00000800001a00001400001400000e00001400000e00000e00000800001400000e00000e00000800000e000008000008000002 0x17000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017 1216 1472)) 0x10117011717ff 0x8000000000000000 (N (N (N (N (N (N (fl 0x391b1a) (fl 0x2d2a26)) (N (fl 0x2b2a0c) e0)) (N (N (fl 0x353332) e0) (N (fl 0x1716) e0))) (N (N (N (fl 0x332b24) e0) (N (fl 0x2d260e) e0)) (N (N (fl 0x1b140c) e0) (N (fl 0x392a1a) e0)))) (N (N (N (N (fl 0x2b2724) (fl 0x2d2b27)) (N (fl 0x1a160e) e0)) (N (N (fl 0xf0c) e0) (N (fl 0x352717) e0))) (N (N (N (fl 0x352726) e0) (N (fl 0x1614) e0)) (N (N (fl 0x2a240c) e0) (N (fl 0x352d1d) e0))))) (N (N (N (N (N (fl 0x2a2624) (fl 0x353226)) (N (fl 0xf0e) e0)) (N (N (fl 0xe0c) e0) (N (fl 0x332717) e0))) (N (N (N (fl 0x2d2726) e0) (N (fl 0x2d2a0e) e0)) (N (N (fl 0x1b1a0c) e0) (N (fl 0x39321a) e0)))) (N (N (N (N (fl 0x332724) (fl 0x39352d)) (N (fl 0x2a260e) e0)) (N (N (fl 0x1a140c) e0) (N (fl 0x322a1a) e0))) (N (N (N (fl 0x332b27) e0) (N (fl 0x1714) e0)) (N (N (fl 0x2b240c) e0) (N (fl 0x272624) e0)))))) (C 11 (C 25 (C 38 (C 37 (C 44 (M 4 0x470d100470c900470c500468c500162a900b68a5008708d004628d00f2eca0052ec60131eaa0091ea60082e8e00c1e7200c1e6a0062e5a0062e5600c1e4e0061e3a0061e36001002300600630060047) (M 2 0xa64b100662b100258a900258a50042ec60041eb20081eaa0021ea600a2e8e0061e720061e6a0061e5a0032e560032e4e0061e3a009008f003005b0060057)) (M 4 0x1470950026469002546901c2e9601c1e9600c1e720081e6a00c1e5a0062e560062e4e0042e3a0051e3a0071e360140087012008301200130020007006005b00200530030047)) (M 2 0x862b100668a500262a500a70990026499002589900e2e9a00e1e9a0061e720061e6a0061e5a0032e560032e4e0041e3a0021e36006001f004001b002000f004000b004007f003005b002004f0020047)) (M 2 0x6686500454650084a6500a4665004386500a2eca0061eb20041eaa0042e9a0041e9a0121e660032e5a0032e4e0061e3a002008b002007b00200770020073008006f0060003003005f006004b)) (M 2 0x37095007702d007622d0082eca0032ec60032e960062e5600e5e2e0122e2e0061e2e0040017006007b004006b00200670050043005003f005003b00300370030033003002f006002b0060027))
def cp_26_2 : CertItem := CI (some (BV 0x2600002000002000001a00002000001a00001a00001400002000001a00001a00001400001a00001400001400000e00002000001a00001a00001400001a00001400001400000e00001a00001400001400000e00001400000e00000e00000800002200001c00001c00001600001c00001600001600001000001c00001600001600001000001600001000001000000a00001c00001600001600001000001600001000001000000a00001600001000001000000a00001000000a00000a000004 0x17000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017 1344 1472)) 0x100010117 0x8000000000000000 (N (N (N (N (N (N (N (fl 0xa0604) (fl 0xd0a06)) (N (fl 0x22120a) e0)) (N (N (fl 0x220a06) e0) (N (fl 0x311913) e0))) (N (N (N (fl 0x130b04) (fl 0x29230b)) (N (fl 0x151312) e0)) (N (N (fl 0x250d07) e0) (N (fl 0x292523) e0)))) (N (N (N (N (fl 0x130704) (fl 0x151307)) (N (fl 0x23130b) e0)) (N (N (fl 0x251506) e0) (N (fl 0x312322) e0))) (N (N (N (fl 0xd0706) (fl 0x312515)) (N (fl 0x311512) e0)) (N (N (fl 0x190b0a) e0) (N (fl 0x70604) e0))))) (N (N (N (N (N (fl 0x220604) (fl 0x252206)) (N (fl 0x190d0b) e0)) (N (N (fl 0x250d06) e0) (N (fl 0x252322) e0))) (N (N (N (fl 0x221204) (fl 0x312212)) (N (fl 0x311312) e0)) (N (N (fl 0x251507) e0) (N (fl 0x312923) e0)))) (N (N (N (N (fl 0x120a04) (fl 0x19120a)) (N (fl 0x25150d) e0)) (N (N (fl 0x230b07) e0) (N (fl 0x312522) e0))) (N (N (N (fl 0x250706) e0) (N (fl 0x191513) e0)) (N (N (fl 0x190d0a) e0) (N (fl 0x131204) e0)))))) (N (N (N (N (N (N (fl 0x120604) (fl 0x151206)) (N (fl 0x29190a) e0)) (N (N (fl 0x150d06) e0) (N (fl 0x311915) e0))) (N (N (N (fl 0x230b04) (fl 0x29250d)) (N (fl 0x191312) e0)) (N (N (fl 0x231307) e0) (N (fl 0x312523) e0)))) (N (N (N (N (fl 0x230704) (fl 0x252307)) (N (fl 0x29190b) e0)) (N (N (fl 0x130b07) e0) (N (fl 0x292522) e0))) (N (N (N (fl 0x150706) (fl 0x312919)) (N (fl 0x311912) e0)) (N (N (fl 0x290b0a) e0) (N (fl 0xb0a04) e0))))) (N (N (N (N (N (fl 0xb0704) (fl 0xd0b07)) (N (fl 0x290d0b) e0)) (N (N (fl 0x221206) e0) (N (fl 0x292322) e0))) (N (N (N (fl 0x231304) (fl 0x312313)) (N (fl 0x191512) e0)) (N (N (fl 0xd0b0a) e0) (N (fl 0x312925) e0)))) (N (N (N (N (fl 0x220a04) (fl 0x29220a)) (N (fl 0x29190d) e0)) (N (N (fl 0x150d07) e0) (N (fl 0x312922) e0))) (N (N (N (fl 0x120a06) e0) (N (fl 0x311513) e0)) (N (N (fl 0x290d0a) e0) (N (fl 0x232204) e0))))))) (C 36 (C 34 (C 9 (C 10 (C 12 (C 6 (C 5 (C 3 (C 33 (C 40 (C 48 (M 2 0x1324d0045449006524900238490067045006584500254450062ed20062eca0062ec60061e9a0061e960061e8e0021e6a0011e6600c1e620021e5a0021e560092e520031e520012e4e0021e3a0021e360021e2e0021e1e00200bb) (W 0x170c500360b100164a500260a5003609500164710016069001324d00270490036849002624900164450092ec20031eaa0031e9a0031e8e0041e620011e5a0012e560042e520061e460011e3a0011e360011e2e0011e1e00300c7)) (M 2 0x668a100564a100650990065095006508d002505900250550065849006524900150490016445006544500650450062ec600c2ec20121ea20021e720021e6a0021e660081e620072e520071e520022e4e0012e4a0011e460021e3a0021e360021e2e0021e1e0060137)) (M 3 0x162a500168990087095008628d0014a8d001708500868850016485009588500954850084c85003427100342690074261003305900330550086451008525100142510033251003304d01b2e8601b1e860051e620011e5200f2e4a0061e4a0151e460031e3a0031e360031e2e0031e1e01b00df)) (M 2 0x2385900250550046251004525100250510024c510024a51002524d0046849006584900350390024a35002622d002601d006700d006640d006540d0044c0d0024a0d002340d002320d006300d0052ec20062e8e0052e860125e0e0163e0e00a2e0e00a1e0e00300df008013700a002b00400fb)) (M 6 0x964a100c62a100f54990035099006648d00c4a610064261003645900354590065855006504d00c584900f5249009504900624390066235006342d0064a1d01270150126815003521500f501500c4615006381500632150123015002300d0322ec20042e860365e160423e1601e2e1601e1e1600400c7004004f0260107028000b)) (C 40 (M 4 0x462950025295008628d006688500658850034c790044665004545900252550024a55002544d002424d002644500852450043845004344500464390044a35004302d00c7019006681900664190065819006541900c42190173019001300d01b2ec20092e9a0245e1a02c3e1a0142e1a0141e1a009012b01c0113001004f01b00f3) (M 2 0x662a10065095004508d004506100650590025055002504d0065845006544500264390022235002502d0024c1d00a70190066819006501900246190024219002381900830190042419002340d002320d0042eca0052ec20042e9a0052e860125e1a0163e1a00a2e1a00a1e1a00b00df002013700a0113004003700a00f3))) (C 48 (C 33 (W 0x13839001683500370310036431003623100354310035231001343100132310012c310012a3100224310032231001502d002500d0024c0d001300d0022ed20012e9a0032e960032e8e0012e4e0022e4a0012e460095e3200b2e320051e320012e1e00100a3006009f003005f0030047004003300200fb) (M 2 0x2508d00468850045485006587900250790025445002683900238350067031006643100662310064c310024a310044231002343100232310022c310022a3100e24310042231002262d002421d0044a0d0122e860125e320162e3200a1e3200a2e0e00e009f00b005f008004f00300470030033)) (M 2 0x660a50026899004508d004688500c60850024c850046039002383500664310126231006603100454310024c310064a31002343100232310022c310022a31002602d002461d00218190026015006700d006600d002540d0122ec20022e4e0082e460125e320162e3200a1e3200b00bf00300b300300ab00e009f00c0033))) (C 48 (C 33 (M 6 0x652690063855005545100b544500664390062835004642d002542d0127029012682901262290125829007522900846290062c29018282900626290182229005521500632150082eca0122e9a0122e9600a2e8e0365e2a0422e2a01e1e2a0062e1e0182e1601b009701b008f00f008b015005700701070150023015000f) (W 0x34a8d00164850035885005426900142550025251002425100164390013235001642d0037029003682900362290034c29003422900138290012c2900328290012629004242900422290092e860095e2a00b2e2a0051e2a0012e1e0042e160060097003008f0030057004010f003002b004000b)) (M 2 0x660a500660990067095006608d00c608500260550026051006545100460390026035002342d00868290126229006602900658290064229002382900232290022c290062829002262900460150122ec20125e2a0162e2a00a1e2a0022e1e0082e1600c00ab0090097009008f005008b002005700c000f0020007))) (C 40 (C 33 (C 48 (M 4 0x44665004545900a524900428390046235002622d002522d00c702500c682500c642500c582500854250024625004382500434250042a2500c2825004262500c24250062ec600c2e9a00c2e960062e8e0245e2602c2e260141e260042e1e0102e1a01c011b019006f0060113003005f003003700300f70190003) (W 0x24c95003608d0014a65001605900352510014c51004604900160390016035001602d00368250076425003602500358250035425001382500134250012a2500328250012625003242500160190092ec20095e2600b2e260051e260062e1a007011b007006f0070003)) (M 6 0x44a8d00e4c85006466500258590044c5900858390066035004722d002422d0126825012642501660250045825008542500e4a25008462500638250063425018282500626250122425012701900e601900a54190362e860062e560062e5200c2e4a0365e260422e2601e1e260062e1e00c00bf02a0083015007b0150073015006f02a004302a001f)) (W 0x158650014c5900150550035049003544500160390016235001622d0017025003682500364250016225001602500258250014a2500346250013825001342500428250042425002701900350190024a190072ec20022e9a0032e520012e4e0095e2600b2e260051e260012e1e009011f0070087007007f0070077002003f002001b0050003))) (C 3 (C 18 (C 40 (C 20 (C 48 (C 33 (M 3 0x9708d00668890096289009588900952890094a890034471003446900344650094c6100644610034459003544d0065445003643900664250036815006301501b2e8a01b1e8a0031e560072e460081e460031e360052e3200c1e320032e2e00b2e260033e1e0082e16015005b0040103) (C 17 (C 9 (M 3 0x6649900354990097089009628900952890094a890096885009588500342710034269009466100942610035459003544d003641901b2e8601b1e860031e660021e620032e560031e3a0031e360142e320031e2e0021e2a0032e1e0083e160092e160041e16001008b012005b) (W 0x162890025889001446500144390016235001622d0037025003682500364250034a25003442500138250013425003421900330190092e860012e5a0012e560012e4e0095e2600b2e260051e260012e1e0012e1a002007b0020073005006f0070043)) (M 2 0x4688900652890064c850024465006446100244590023055002304d0067045006584500654450064a4500644450023845002344500430190122e8600a2e460161e460025e3a0025e360045e3200a1e320025e2e0055e2a0025e1e0015e1a00e0083009005b00e004f))) (M 8 0x2060b900860ad01260a9012708d0067089018688901862890185889018528900444710064669006446500234650184c610184a6100454590043859002544d0086039008603501860310204431008602d0186425018602500844250186015018441500830150482e8a0481e8a0081e560061e4e0202e460181e4602d2e2a0082e1e0053e1a0281e1a04800d300b005b)) (M 2 0x2648d0024c8d0047089004628900258890044a8900c4471002446900144650026855002705100262510045851006545100652510024a5100644510013251002304d00228350022c3100a2831002642d0044c2900246290082829004682500264250044425004282500330150122e8a0061e8a00a2e520161e520021e3a0021e1e00c5e1a0061e1601200d300900af002005f0050107)) (M 2 0x664a50086ca1006508d006708900668890066289006588900250890064a8900244710024c6900244650044c610025059002505500650510084451002504d0085445006504500650150122e8a0121e8a0021e3a0012e360011e360011e320022e2e00b2e260022e1e0082e1a0061e1a0083e1601200eb01200cf00a009f00e0123003007f)) (M 4 0x44c8d004466900454590046855004544d00c70490046849008624900c584900c52490084c49004464900438490043249004544500424390044a350084a3100c2431004642d00c442501024250046815004621500844150242e8a0241e8a0142e4a02c1e4a0061e320041e1e00a1e1602400cf024012f00f00bb00d00a700b00a301c009301c00670020047)) (M 2 0x268b100244710064461002445900262550026251002585100452510024a510044451002524d00244390026835002683100444310082231002622d00258250044a250023015006700d006640d006540d0064c0d002340d002320d006300d0122e8a0125e0e0163e0e00a2e0e00a1e0e01200eb01200ff00e002f00e0027001001b00e001700500070070003))) (C 20 (C 40 (C 12 (C 5 (C 48 (C 18 (C 34 (C 33 (M 6 0x1070a5002689500358950024c95002709101062910025491002528d010488d01048650104c6100a4a6101048610062629002622500f482500a22250106819002641900f58190063819010640d010540d006340d0362e920361e920062e5a0061e5600e2e460131e460061e3a0061e360062e2e0232e2a00f1e260062e1e0031e1a0042e0e) (C 3 (M 2 0x368a50036899001649100662910065491003528d003488d0067085005648500658850034c850044a6100648610024859001424d0023845003422900234250122e860121e860021e660041e620022e560011e4e0021e3a0022e360021e2e0052e2a0061e2a0023e1e0063e1a0082e1a00c0083) (W 0x1524d00164390013835001622d00348290012c290043019003700d001640d002620d001540d002520d003480d001340d001320d003300d0092e860095e0e00b3e0e0052e0e0051e0e007002b007001f003000f))) (M 2 0x65291006548d00670890066889006628900658890064a89002488900344650084c6100648610022c29001262900822290066425001262500122250122e8a0121e8a0021e720021e6a0021e560051e460021e3a0022e360022e2e0032e2a0061e260021e1e0043e0e00a2e0e01200cb00e0117)) (M 2 0x64c950066291006549100670490065849006524900648490064649002384900224390022a35002242d0022c290022629006642500648250022425002340d002320d0122e920121e9200a2e4a0161e4a0021e1e0011e1a0071e0e01200cb00e00a700a00570030013)) (M 4 0x460b500a60b100c60a50107491002709100c649100c629100c549100c488d0044a710024869004486500c4c610084a610025859002345900460390046035004602d01c602900c6825010482500a700d00c600d0242e920241e920041e560041e4e0142e4a0031e4a00f1e460043e1e0083e1a0141e1a0063e0e02400e702400db00800b700500ab)) (M 5 0x5486900f486100338590025255005544d002624900d524900f4849005324900d464500348390022c390056235003622d002462d00f6429005622900c48290032229003602500a542500344250032a2500f701500f681500f581500f4c150023815014301502d2e9202d5e160373e160192e160191e1602a00e702d010b023003b01300070100003)) (C 48 (M 2 0x14c95004488d0025271002486900248590024855002524d002484900448450024645002683900268350047031002683100664310066231001543100152310054c310054a31002323100a24310082231001542d001522d00270250045425001481d0122e920125e320162e3200a1e320012e1e0092e0e01000cb00b008b003007b003006f00e006300e004b002002f002001f) (M 2 0x660990066095002488d0026039002603500664310066231006603100654310065231002343100232310022c310022a31002602d006602500446250023825002481d006700d006600d002480d0122e920022e4e0082e4a0125e320162e3200a1e3201200e701200db00300c300b00b700300ab002006f002006300c010f00e004b))) (C 6 (M 4 0xc68a500e6ca100c5095004729100c709100c649100c629100c5491002508d0064869004486500c4c6100a466100450590045055004504d00c504900e484900c58450105045004302d0043829002302900a500d00c480d0242e920241e920022e4a0042e3a0042e3600f2e2a0152e260042e1e0082e160141e160062e0e02400ef02400e302400d701c01270070077) (W 0x1505900150550035049002464900350450034845001464500164390016235001322d002622900352290026425003482500126250037019003681900350190034a19001381900134190033019003300d0092e920095e1a00b3e1a0052e1a0051e1a00900ef00900d7001008700901170070063007003b0020013002000f))) (C 33 (M 6 0xc64c5010708d002488d00638590025855004505500270510105851012545101252510124c510124a5100634510063251006624d0064839006483500c48290122829006642500c48250182825010480d0362e920361e9201e2e520361e520062e2e0081e2a0063e1e0161e0e03200e3036013301500bb01500af01500a302a009b02a006b02a00530040027) (M 2 0x6488d006648500458850064261002385900258550067051006545100652510064c5100642510023451002325100228390022835002422d006482900442290042829006282500226250122e860121e8600a2e520161e520021e1e0071e160011e0e01200d701200cb012013300400bb00400af00a00a300e009b00e006b006001f007000b))))
def cp_26_3 : CertItem := CI (some (BV 0x2800002200002200001c00002200001c00001c00001600002200001c00001c00001600001c00001600001600001000002200001c00001c00001600001c00001600001600001000001c00001600001600001000001600001000001000000a00002400001e00001e00001800001e00001800001800001200001e00001800001800001200001800001200001200000c00001e00001800001800001200001800001200001200000c00001800001200001200000c00001200000c00000c000006 0x17000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017 1472 1472)) 1 0x8000000000000000 (N (N (N (N (N (fl 0x50302) (fl 0x110905)) (N (fl 0x210902) e0)) (N (N (fl 0x90502) e0) (N (fl 0x210503) e0))) (N (N (N (fl 0x110302) (fl 0x211105)) (N (fl 0x90503) e0)) (N (N (fl 0x210502) e0) (N (fl 0x210903) e0)))) (N (N (N (N (fl 0x90302) (fl 0x210905)) (N (fl 0x211102) e0)) (N (N (fl 0x110502) e0) (N (fl 0x110903) e0))) (N (N (N (fl 0x210302) (fl 0x211109)) (N (fl 0x110503) e0)) (N (N (fl 0x110902) e0) (N (fl 0x211103) e0))))) (C 2 (C 4 (C 1 (C 5 (C 3 (C 9 (C 10 (C 12 (C 6 (C 44 (C 36 (C 32 (M 2 0x1284900a4445002544100252410024c410024a2100246210022821002242100c2ec200e1ea20041e8a00a2e860041e8600a1e620071e520071e4a00e2e420021e4200e1e22) (C 8 (M 2 0x26095002608d00270890026889005628900252890026485003608500254850024c85003445100442510045049001424900a50450162e820161e8200a1e620031e520051e4a00e2e420081e42) (W 0x3426100442510016821001642100162210014c210014a2100146210012821001242100b2e820042e4a0032e4600b5e2200d2e220071e2200b004f))) (W 0x17091001649100162910015491001529100b5091001488d0034a8900168850014c850024885002425100448490014249004444500440210022e9200b1e920092e820051e620031e520012e460062e420051e420071e22)) (M 2 0x26095002649100262910015291002608d0017089002688900a588900152890017085009588500254850024c85007504900348490045845006484500a584100b1eb20071ea20162e820041e8200a1e6200a2e520042e420081e420082e2200e1e22)) (W 0x128450012445001544100152410014a41001464100128210012421001222100170190056019005501900542190053019001241900110190032e8a0022e860062e8200b5e1a00d3e1a0072e1a0071e1a007004f)) (W 0x142610016431001623100560310054431005423100130310042431005223100146210014219003301900118190062e920022e8a0032e820052e520012e4a0012e4200b5e3200d2e320071e3200a004f)) (M 2 0x142610014231005343100230310016829002622900a602900a482900a42290073029009282900a2229002182900168210024a2100264190046019002461900242190021e9a0012e9200e2e8a0072e820012e5200a2e4a0032e420145e2a01a2e2a00e1e2a013004f)) (M 2 0x1488d00444310023231002303100262290025829002322900230290026825002642500a602500a482500a4425006302500a282500a2425002182500214250024c2100250190024a19004421900210190032e920012e8e00a2e860082e8200a2e460042e420165e2601a2e2600e1e26012004f)) (M 4 0x75049004684500228450044c410044a410014431005423100a22310042031006482900626290042429002482501228250096021004222100364190045819009501900d700d001620d013600d004540d004520d00c500d014480d014300d009240d001200d004140d0040c0d0172e860152e8202c5e0e0343e0e01c2e0e01c1e0e01f004f)) (M 3 0x348490084445001544100650410034c410014641003683100560310032431001223100a4829005422900628250062425003222500246210032821003242100160190035819002541900328190031019009701500f601500f501500d441500e3015003281500318150030c15003640d003620d003520d0024a0d001300d003220d0102e860112e820215e160273e160152e160151e16016004f)) (C 32 (C 8 (M 4 0x760490034849001284900a50410104841009444100c223100420310042629008222900420290044a2500f282500124250103019001201900c50150074415004520d006500d009480d0010a0d00e700501468050146405004580500a54050044c05004300500428050082405004180500414050030c050042e8e00c2e8a01c2e8602c5e060343e0601c2e0601c1e06) (M 2 0x64431006222900218290086021003482100844210062a21002282100826210022421008301900560150055015008480d002220d00a700500268050026405005580500a54050024c05002300500828050082405002180500214050020c050012ec20022e960032e920022e8e00e2e860165e0601a3e0600e2e0600e1e06016001f)) (M 2 0x24a6100152510044051002305100748490013049001524500750450024445001603100740310056029003482900148250084425001282500750190013019004601500246150044415002620d004600d002480d002320d002700500668050026405009580500254050024c05004300500228050022405002180500214050020c050162e820165e0601a3e0600e2e0600e1e0601600270160023))) (C 32 (C 1 (C 34 (M 4 0x4585100d604900142410034231001243100f223100e2829002202900b50250033025002282500224210012221007421900d301900e601500250150044c15004701101164110056211004541100f521100446110043011004241100422110041411004121100f500d005480d0042e960172e920112e8602c5e120343e1201c2e1201c1e120290043) (M 4 0x2588500844710035051010425100a504900244490045041006423100e223100b5029004422900128290104425004242100e601900258190044a1900c4415008301500870110066411004621100f54110045211004461100c3011004241100422110041411004121100e600d002220d004080d02c2e8a02c5e120343e1201c2e1201c1e120280043)) (W 0x14445002443100222310012429002222900328250022425001601900350190046011004501100444110023211001301100124110011411001620d002600d001520d001320d001700500568050016405005580500454050054c05004300500128050012405001180500114050010c050032e920012e8e0072e8600b5e0600d3e060072e060071e0600b001700b0013)) (M 2 0x24061002445100842510025849005504900550450023045001244500460310024a31004423100840290084425002681900460190024219002301900250150024c150044415002301500470110026411002621100a54110025211002461100230110022411002221100214110021211006600d002500d002080d0162e820165e1201a3e1200e2e1200e1e12016004b0160047016001b))) (C 32 (C 1 (C 4 (C 8 (M 3 0x65049002284500354410035041008484100c424100922310032031005422900a282900924250032025004601900b3019003601500550150034c150013015007500d008480d006700900b680900f6209003580900352090044a09003300900328090032209003180900312090030a090052e920032e8e0152e8a0042e860215e0a0273e0a0152e0a0151e0a) (W 0x24231003242500118250046021004482100442210032c210012821004262100122210014219004301900350150012215003480d002240d005700900168090016209005580900552090014a09001300900428090032209001180900112090010a090022ec20012e9a0012e8e0072e8a00b5e0a00d3e0a0072e0a0071e0a00b0037)) (W 0x142450032c3100128310024229002222900524250016015003501500460110045011004421100434110012211001640d002600d001540d001140d001700900568090026209005580900252090054a0900530090042809001220900118090010a090032e920012e8e0072e8a00b5e0a00d3e0a0072e0a0071e0a00b002f00b002b)) (W 0x14245003223100226290012429001222900248250032825001601900350190046015001501500262090026009001520900350090044809004320900128090011809001700500168050036405002580500454050054c05005300500128050032405001180500114050010c050052e8a0062e8600b5e0600d3e060072e060071e0600b000b00b000700b0003)) (M 2 0x6426100350510054251001504900848490014249006404500760310014031007602900148290024629001642500548250025419004501900242190023419004401500222150021215001640d006500d0024c0d002700900268090086209003580900252090064a09004300900228090022209002180900212090020a090162e820011e0e0165e0a01a3e0a00e2e0a00d1e0a016003f016003b0160033016000f)))
def cp_26_4 : CertItem := CI (some (BV 0x2a00002400002400001e00002400001e00001e00001800002400001e00001e00001800001e00001800001800001200002400001e00001e00001800001e00001800001800001200001e00001800001800001200001800001200001200000c00002600002000002000001a00002000001a00001a00001400002000001a00001a00001400001a00001400001400000e00002000001a00001a00001400001a00001400001400000e00001a00001400001400000e00001400000e00000e000008 0x17000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017000017 1600 1472)) 0 0x8000000000000000 e0 (C 4 (C 0 (C 32 (M 2 0x260850062809002500500248050024405006300500524050022ec20082e920082e8a0082e860011e4a0061e460121e420061e320061e2a0061e2600d5e220052e220062e1a0062e160015e0e0052e0e00c5e0a0012e06) (M 2 0x260850024061002425100240510064249002600900250090024809002280900622090020a0900250050024805002440500430050061805001140501a2e8201a1e820121e420051e2a0061e2600b2e220071e220062e1a0042e160062e0e0022e0a0013e06)) (M 4 0x6422900c4425004602100448210044221006242100c22210064219006101900c2015006300d006200d004600900450090074809006300900c2809003180900460050034c05004480500444050062405009180500614050042e8a0042e8602c2e820345e0203c3e020242e020241e02)) (W 0x32025003682100160210052021002501900142190044415002301500460110015011001441100342110033011001241100322110031411001200d002080d00150090024a0900142090033009002280900150050022405003180500308050022e9200b2e8200d3e120092e120091e1200d5e020023e02))
def cp_26_5 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x92e820071e420011e260071e220011e1a0012e160072e120012e0e0053e0a0022e0a0025e060053e0600d5e02)
def cp_26_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x51e120051e0a0022e060031e0600b2e02)
def wVec_27 : Fin 6 → ℕ := ![2,2,2,2,2,2]
def fastW_27 (m : ℕ) : ℕ := cond (bitAt m 0) 2 0 + cond (bitAt m 1) 2 0 + cond (bitAt m 2) 2 0 + cond (bitAt m 3) 2 0 + cond (bitAt m 4) 2 0 + cond (bitAt m 5) 2 0
def cFn_27 (k i : ℕ) : ℕ × ℕ := (fastW_27 i + 1 * k, 9)
def rowZ_27 : ℕ → List ℕ
  | 0 => (unpackBytes 49 0x2f2e2c281f1e1c1839353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 26 0xf0e0c0831292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowO_27 : ℕ → List ℕ
  | 0 => (unpackBytes 3 0x403020)
  | _ => []
def rowFl_27 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x3d3a36)
  | 1 => (unpackForbs 36 0x3935330000000000393532000000000039333200000000003533320000000000392d2b0000000000392d2a0000000000392b2a00000000002d2b2a0000000000352d270000000000332b270000000000352d260000000000322a26000000000035272600000000002d27260000000000332b240000000000322a24000000000033272400000000002b2724000000000032262400000000002a26240000000000391d1b0000000000391d1a0000000000391b1a00000000001d1b1a0000000000351d170000000000331b170000000000351d160000000000321a16000000000035171600000000001d17160000000000331b140000000000321a14000000000033171400000000001b1714000000000032161400000000001a1614)
  | 2 => (unpackForbs 30 0x39352d000000000039332b000000000039322a000000000035332700000000002d2b27000000000035322600000000002d2a26000000000033322400000000002b2a240000000000272624000000000039351d0000000000392d1d0000000000352d1d000000000039331b0000000000392b1b0000000000332b1b000000000039321a0000000000392a1a0000000000322a1a00000000003533170000000000352717000000000033271700000000001d1b17000000000032261600000000001d1a1600000000003332140000000000332414000000000032241400000000001b1a140000000000171614)
  | 3 => (unpackForbs 58 0x393733000000000039343300000000003d39320000000000373532000000000037352d000000000034332b00000000003a2d2a00000000002f2d2a000000000036352700000000003b3327000000000034332700000000003432260000000000352e2600000000003a2a2600000000002c2a26000000000037332400000000002e2a24000000000034272400000000002c272400000000002e262400000000003a391d000000000037351d00000000003a391b000000000034331b00000000002b1f1b00000000003b1d1b00000000001e1d1b000000000034321a00000000002c2a1a00000000003a1d1a00000000003b1b1a00000000003a1b1a00000000003635170000000000351f170000000000271f170000000000371d1700000000001c1b170000000000351817000000000037351600000000003a321600000000002e261600000000002826160000000000361d1600000000001c1a160000000000321816000000000037171600000000001f171600000000003b3314000000000037331400000000002c24140000000000341b1400000000001f1b1400000000003a1a140000000000341a1400000000001b181400000000001a181400000000003717140000000000341614)
  | 4 => (unpackForbs 60 0x3129250000000000312923000000000031252300000000002925230000000000312922000000000031252200000000002925220000000000312322000000000029232200000000002523220000000000311915000000000031191300000000003115130000000000191513000000000031191200000000003115120000000000191512000000000031131200000000001913120000000000151312000000000029190d000000000025150d000000000029190b000000000023130b0000000000290d0b0000000000190d0b000000000029190a000000000022120a0000000000290d0a0000000000190d0a0000000000290b0a0000000000190b0a00000000000d0b0a000000000025150700000000002313070000000000250d070000000000150d070000000000230b070000000000130b07000000000025150600000000002212060000000000250d060000000000150d060000000000220a060000000000120a060000000000250706000000000015070600000000000d0706000000000023130400000000002212040000000000230b040000000000130b040000000000220a040000000000120a040000000000230704000000000013070400000000000b07040000000000220604000000000012060400000000000a0604)
  | 5 => (unpackForbs 20 0x312919000000000031251500000000003123130000000000312212000000000029250d000000000019150d000000000029230b000000000019130b000000000029220a000000000019120a0000000000252307000000000015130700000000000d0b070000000000252206000000000015120600000000000d0a060000000000232204000000000013120400000000000b0a040000000000070604)
  | 6 => ((unpackForbs 64 0x260a0600000000001a0a060000000000160a0600000000000c0a06000000000025080600000000002208060000000000150806000000000012080600000000000d080600000000000a0806000000000027070600000000002607060000000000170706000000000016070600000000000f070600000000000e0706000000000033230400000000002b23040000000000272304000000000032220400000000002a22040000000000262204000000000023140400000000002214040000000000331304000000000024130400000000001b130400000000001713040000000000321204000000000024120400000000001a120400000000001612040000000000230c040000000000220c040000000000130c040000000000120c0400000000002b0b040000000000240b0400000000001b0b040000000000140b0400000000000f0b0400000000002a0a040000000000240a0400000000001a0a040000000000140a0400000000000e0a04000000000023080400000000002208040000000000130804000000000012080400000000000b080400000000000a0804000000000027070400000000002407040000000000170704000000000014070400000000000f070400000000000c0704000000000026060400000000002406040000000000160604000000000014060400000000000e060400000000000c0604) ++ (unpackForbs 64 0xf0b0a00000000000e0b0a000000000035250700000000002d25070000000000262507000000000033230700000000002b23070000000000242307000000000025170700000000002317070000000000351507000000000027150700000000001d150700000000001615070000000000331307000000000027130700000000001b130700000000001413070000000000250f070000000000230f070000000000150f070000000000130f0700000000002d0d070000000000270d0700000000001d0d070000000000170d0700000000000e0d0700000000002b0b070000000000270b0700000000001b0b070000000000170b0700000000000c0b07000000000025080700000000002308070000000000150807000000000013080700000000000d080700000000000b0807000000000035250600000000002d25060000000000272506000000000032220600000000002a22060000000000242206000000000025160600000000002216060000000000351506000000000026150600000000001d150600000000001715060000000000321206000000000026120600000000001a120600000000001412060000000000250e060000000000220e060000000000150e060000000000120e0600000000002d0d060000000000260d0600000000001d0d060000000000160d0600000000000f0d0600000000002a0a06) ++ (unpackForbs 64 0x39290b00000000002d290b00000000002a290b000000000033230b000000000027230b000000000024230b0000000000291b0b0000000000231b0b000000000039190b00000000002b190b00000000001d190b00000000001a190b000000000033130b00000000002b130b000000000017130b000000000014130b0000000000290f0b0000000000230f0b0000000000190f0b0000000000130f0b00000000002d0d0b00000000002b0d0b00000000001d0d0b00000000001b0d0b00000000000e0d0b0000000000290c0b0000000000230c0b0000000000190c0b0000000000130c0b00000000000d0c0b000000000039290a00000000002d290a00000000002b290a000000000032220a000000000026220a000000000024220a0000000000291a0a0000000000221a0a000000000039190a00000000002a190a00000000001d190a00000000001b190a000000000032120a00000000002a120a000000000016120a000000000014120a0000000000290e0a0000000000220e0a0000000000190e0a0000000000120e0a00000000002d0d0a00000000002a0d0a00000000001d0d0a00000000001a0d0a00000000000f0d0a0000000000290c0a0000000000220c0a0000000000190c0a0000000000120c0a00000000000d0c0a00000000002b0b0a00000000002a0b0a00000000001b0b0a00000000001a0b0a) ++ (unpackForbs 64 0x23171300000000001917130000000000351513000000000033151300000000001d151300000000001b1513000000000016151300000000003114130000000000231413000000000019141300000000001514130000000000393112000000000035311200000000002a2212000000000026221200000000002422120000000000311a120000000000221a120000000000391912000000000032191200000000001d191200000000001b19120000000000311612000000000022161200000000001916120000000000351512000000000032151200000000001d151200000000001a1512000000000017151200000000003114120000000000221412000000000019141200000000001514120000000000331312000000000032131200000000001b131200000000001a131200000000001713120000000000161312000000000039290d00000000002b290d00000000002a290d000000000035250d000000000027250d000000000026250d0000000000291d0d0000000000251d0d000000000039190d00000000002d190d00000000001b190d00000000001a190d000000000035150d00000000002d150d000000000017150d000000000016150d0000000000290f0d0000000000250f0d0000000000190f0d0000000000150f0d0000000000290e0d0000000000250e0d0000000000190e0d0000000000150e0d) ++ (unpackForbs 64 0x312a220000000000392922000000000032292200000000002d292200000000002b2922000000000031262200000000002926220000000000352522000000000032252200000000002d252200000000002a252200000000002725220000000000312422000000000029242200000000002524220000000000332322000000000032232200000000002b232200000000002a23220000000000272322000000000026232200000000003531190000000000333119000000000032311900000000002d291900000000002b291900000000002a29190000000000311d190000000000291d190000000000311b190000000000291b190000000000311a190000000000291a1900000000003931150000000000333115000000000032311500000000002d2515000000000027251500000000002625150000000000311d150000000000251d150000000000391915000000000035191500000000001b191500000000001a191500000000003117150000000000251715000000000019171500000000003116150000000000251615000000000019161500000000003931130000000000353113000000000032311300000000002b2313000000000027231300000000002423130000000000311b130000000000231b130000000000391913000000000033191300000000001d191300000000001a19130000000000311713) ++ (unpackForbs 38 0x353129000000000033312900000000003231290000000000312d290000000000312b290000000000312a29000000000039312500000000003331250000000000312d250000000000392925000000000035292500000000002b292500000000002a292500000000003127250000000000292725000000000031262500000000002926250000000000393123000000000035312300000000003231230000000000312b230000000000392923000000000033292300000000002d292300000000002a2923000000000031272300000000002927230000000000352523000000000033252300000000002d252300000000002b25230000000000262523000000000031242300000000002924230000000000252423000000000039312200000000003531220000000000333122))
  | 7 => (unpackForbs 20 0x2111090000000000211105000000000021090500000000001109050000000000211103000000000021090300000000001109030000000000210503000000000011050300000000000905030000000000211102000000000021090200000000001109020000000000210502000000000011050200000000000905020000000000210302000000000011030200000000000903020000000000050302)
  | 8 => ((unpackForbs 64 0x191103000000000015110300000000001211030000000000210b030000000000110b0300000000002309030000000000190903000000000013090300000000000d090300000000000a0903000000000021070300000000001107030000000000090703000000000025050300000000002305030000000000150503000000000013050300000000000d050300000000000b05030000000000060503000000000021040300000000001104030000000000090403000000000005040300000000003121020000000000292102000000000025210200000000002321020000000000211202000000000031110200000000002211020000000000191102000000000015110200000000001311020000000000210a020000000000110a02000000000029090200000000002209020000000000190902000000000012090200000000000d090200000000000b0902000000000021060200000000001106020000000000090602000000000025050200000000002205020000000000150502000000000012050200000000000d050200000000000a050200000000000705020000000000210402000000000011040200000000000904020000000000050402000000000023030200000000002203020000000000130302000000000012030200000000000b030200000000000a030200000000000703020000000000060302) ++ (unpackForbs 55 0x292111000000000025211100000000002321110000000000222111000000000021191100000000002115110000000000211311000000000021121100000000003121090000000000252109000000000023210900000000002221090000000000211909000000000031110900000000002911090000000000151109000000000013110900000000001211090000000000210d090000000000110d090000000000210b090000000000110b090000000000210a090000000000110a0900000000003121050000000000292105000000000023210500000000002221050000000000211505000000000031110500000000002511050000000000191105000000000013110500000000001211050000000000210d050000000000110d05000000000029090500000000002509050000000000190905000000000015090500000000000b090500000000000a09050000000000210705000000000011070500000000000907050000000000210605000000000011060500000000000906050000000000312103000000000029210300000000002521030000000000222103000000000021130300000000003111030000000000231103))
  | _ => []
def rowFbs_27 : ℕ → List (List ℕ)
  | 0 => (rowFl_27 0)
  | 1 => (rowFl_27 1) ++ (rowFl_27 2) ++ (rowFl_27 3)
  | 2 => (rowFl_27 4) ++ (rowFl_27 5) ++ (rowFl_27 6)
  | 3 => (rowFl_27 7) ++ (rowFl_27 8)
  | _ => []
def cp_27_0 : CertItem := CI (some (BV 0xc00000a00000a00000800000a00000800000800000600000a00000800000800000600000800000600000600000400000a00000800000800000600000800000600000600000400000800000600000600000400000600000400000400000200000a000008000008000006000008000006000006000004000008000006000006000004000006000004000004000002000008000006000006000004000006000004000004000002000006000004000004000002000004000002000002000000 0x9000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009 384 576)) 0x1177fff7fff7ffe 0x8000800080000000 (fl 0x3d3a36) (C 53 (M 2 0x278e500174d900174cd0016ccd) (M 2 0x178d500172d50026cd500274cd0010003))
def cp_27_1 : CertItem := CI (some (BV 0xd00000b00000b00000900000b00000900000900000700000b00000900000900000700000900000700000700000500000b00000900000900000700000900000700000700000500000900000700000700000500000700000500000500000300000b000009000009000007000009000007000007000005000009000007000007000005000007000005000005000003000009000007000007000005000007000005000005000003000007000005000005000003000005000003000003000001 0x9000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009 448 576)) 0x1011701177fff 0x8000000000000000 (N (N (N (N (N (N (N (fl 0x1a1614) (fl 0x39332b)) (N (fl 0x353332) (fl 0x34321a))) (N (N (fl 0x2a2624) (fl 0x1c1a16)) (N (fl 0x392a1a) (fl 0x343226)))) (N (N (N (fl 0x321a16) (fl 0x1f1b14)) (N (fl 0x333214) (fl 0x2e2624))) (N (N (fl 0x322a26) (fl 0x371d17)) (N (fl 0x272624) (fl 0x373532))))) (N (N (N (N (fl 0x321a14) (fl 0x1a1814)) (N (fl 0x171614) (fl 0x34331b))) (N (N (fl 0x322a24) (fl 0x3a3216)) (N (fl 0x39331b) (fl 0x2f2d2a)))) (N (N (N (fl 0x1d1b1a) (fl 0x3b3314)) (N (fl 0x332717) (fl 0x373324))) (N (N (fl 0x2d2b2a) (fl 0x3a1b1a)) (N (fl 0x353226) e0))))) (N (N (N (N (N (fl 0x1b1714) (fl 0x341614)) (N (fl 0x393532) (fl 0x3b1d1b))) (N (N (fl 0x2b2724) (fl 0x282616)) (N (fl 0x332b1b) (fl 0x3b3327)))) (N (N (N (fl 0x331b17) (fl 0x2c2414)) (N (fl 0x322616) (fl 0x342724))) (N (N (fl 0x332b27) (fl 0x351f17)) (N (fl 0x333224) (fl 0x393433))))) (N (N (N (N (fl 0x1d1716) (fl 0x341a14)) (N (fl 0x322414) (fl 0x37351d))) (N (N (fl 0x2d2726) (fl 0x351817)) (N (fl 0x392d1d) (fl 0x34332b)))) (N (N (N (fl 0x391d1a) (fl 0x371716)) (N (fl 0x353317) (fl 0x3a2a26))) (N (N (fl 0x392d2a) (fl 0x3a1d1a)) (N (fl 0x353327) e0)))))) (N (N (N (N (N (N (fl 0x321614) (fl 0x39352d)) (N (fl 0x393332) (fl 0x1e1d1b))) (N (N (fl 0x322624) (fl 0x361d16)) (N (fl 0x39321a) (fl 0x343327)))) (N (N (N (fl 0x351d16) (fl 0x341b14)) (N (fl 0x1d1a16) (fl 0x2c2724))) (N (N (fl 0x352d26) (fl 0x271f17)) (N (fl 0x2b2a24) (fl 0x3d3932))))) (N (N (N (N (fl 0x331b14) (fl 0x1b1814)) (N (fl 0x1b1a14) (fl 0x3a391b))) (N (N (fl 0x332b24) (fl 0x373516)) (N (fl 0x352d1d) (fl 0x3a2d2a)))) (N (N (N (fl 0x391b1a) (fl 0x1f1716)) (N (fl 0x352717) (fl 0x2c2a26))) (N (N (fl 0x392b2a) (fl 0x3b1b1a)) (N (fl 0x2d2b27) e0))))) (N (N (N (N (N (fl 0x331714) (fl 0x371714)) (N (fl 0x393533) (fl 0x2b1f1b))) (N (N (fl 0x332724) (fl 0x2e2616)) (N (fl 0x392b1b) (fl 0x363527)))) (N (N (N (fl 0x351d17) (fl 0x373314)) (N (fl 0x1d1b17) (fl 0x2e2a24))) (N (N (fl 0x352d27) (fl 0x363517)) (N (fl 0x2d2a26) (fl 0x393733))))) (N (N (N (N (fl 0x351716) (fl 0x3a1a14)) (N (fl 0x332414) (fl 0x3a391d))) (N (N (fl 0x352726) (fl 0x1c1b17)) (N (fl 0x39351d) (fl 0x37352d)))) (N (N (N (fl 0x391d1b) (fl 0x321816)) (N (fl 0x322a1a) (fl 0x352e26))) (N (N (fl 0x392d2b) (fl 0x2c2a1a)) (N (fl 0x39322a) e0))))))) (C 50 (C 41 (C 26 (C 52 (C 49 (C 38 (C 25 (C 37 (C 22 (C 19 (M 3 0x2705500446550021eb20021eaa0021e8e0061e72004007f) (W 0x254710024655002704d0021eb20021e4e)) (W 0x270590024659002544d0021eb20021e5a002001b)) (C 19 (W 0x27095002589500254710024a590021e960021e5600201a3) (M 5 0x84a7100258590025855004704d006544d00a4a4d00a1e8e00a1e4e004007f00200db0080093))) (C 37 (C 19 (W 0x25865002466500270590021eaa0021e6600200a7) (W 0x2544d002464d0022c4d0021eb20021e4e002003b002011b00201130020003)) (M 2 0x1589500254710044a65004466500158590034a590014a4d0041e960041e66002007f002003b001014f0030003))) (C 35 (C 37 (C 22 (M 2 0x270990024c71001586500154650044c4d0041e9a0041e5600300f7002003b) (W 0x15465001705900158590034c590024c550021e9a0021e5a00100f7001003b0010163002010f)) (W 0x270990024c950024a650024a59002544d0021e960021e72002005b002014b)) (W 0x2708d0024c7100258650024655002464d0021e8e0021e5a00201ab002004b00200e3))) (C 25 (C 21 (C 22 (C 19 (M 5 0x270b100462b100a62a900a629900670950041eb20061e8e00a1e7200201e70040047) (M 3 0x66271003704d003544d0014c4d0054a4d0021eb20041e9a0061e4e003007f001005b006009b)) (W 0x262b100262a9002705900262590024c590021e960021e5a0020163002009b)) (W 0x270990026255002585500246550022c550021eaa0021e5600200ab0020147002013f0020007)) (W 0x262650025865002546500262590021e9a0021e66002004700200c7002017b00200230020013))) (C 38 (C 28 (C 22 (C 56 (C 35 (W 0x268a90026865002684d0021eb20021e5600200f3) (W 0x268a9002688d00246650021e8e0021e560020067002009b)) (W 0x268a9002688d0026865002704d0021e960021e56002008b0020107)) (W 0x26895002686500170590026859001545900246590022c4d0011eb20011eaa0021e5a00201e3002016f002015b002001f)) (W 0x254710026865002684d0021e8e0021e7200200f300200df00200d7002002f0020027)) (W 0x268c50027099002689900268650024c4d0021e9a0021e5600201cf002006f002005f002004b002019b00200b7))) (C 25 (C 19 (C 22 (C 28 (C 35 (C 44 (W 0x2686900262690024c550021e960021e6a00200cf) (W 0x26269002586900258550021eb20021e6a0010067001005b00200cf)) (W 0x2688d0024c69002466900258550021e8e0021e6a002004700200cf)) (W 0x24a7100262690024c69002386900238550021e8e0021e6a00200d7002018f002003f0020187)) (W 0x246690026259002585900634590021e960021e5a00200cf002016b002016700200af0020137)) (M 2 0x3686900158690043869002704d004624d002544d0014c4d0034a4d004464d0042a4d0031eb20011e9a0041e4e001005f00200cf008012700401230040117004000b)) (W 0x258690025469001686500162650014a65002466500434650021e9a0021e6600100f30020177001017300200370020033002015f00201430020097))) (C 25 (C 35 (C 56 (C 44 (C 37 (C 19 (C 49 (W 0x268a5002526900254590024c550021ea60021e72) (W 0x268a900262a50026299002527100252690021ea60021e5a0020153)) (W 0x268a90025271002524d0024c4d0021ea60021e4e002000b0020007)) (W 0x254a500252950024c71002526900252550024a4d0021e960021e5a00201bf002006300201b7)) (W 0x262a5002589900258590025255002524d0021ea60021e6a00201d700201d3002007300200ef00200d7)) (W 0x670a500268a5001709900170590014c55002524d0021ea60011e5a00200ff002007b002007700201bb002019f0020197)) (W 0x258a5002708d004528d0025271002686900246550021e8e0021e5a002005300201af00200e700201a70020043002012b)) (W 0x2528d00252690026865008526500254590024c550021ea60021e6600201d700201bb00200c300200bf002017f002017b002011f))) (C 49 (C 22 (C 52 (C 19 (C 26 (C 35 (C 28 (C 41 (W 0x264b1002649500264650021e9a0021e560020103) (W 0x264a5002649500252550021ea60021e66002007b002006b)) (W 0x264710025271002646500264550021e960021e72002006b00200db)) (W 0x264b1002648d002466500246550021e8e0021e7200201eb0020057002004f0020043)) (W 0x2648d004646900258690015269001646500264550011ea60011e960021e6a00201cb00200d3002019300200cb002018b)) (W 0x270c90026471004644d002524d0024a4d0021eb20021e4e002006b0020133002009f0020017002011b002010b)) (W 0x868c900264a50026495002647100268650021eaa0021e6a002008f00201df00200fb00201b30020157002012f)) (W 0x26465006645900258590024a590021ea60021e5a00201ef002005700200bb00200b30020163002002b002013b002000f)) (W 0x864c500264b10026271002626900262590021ea60021e560020087002008300201db00201c700201c300200eb002018300200a3)))
def cp_27_2 : CertItem := CI (some (BV 0xe00000c00000c00000a00000c00000a00000a00000800000c00000a00000a00000800000a00000800000800000600000c00000a00000a00000800000a00000800000800000600000a00000800000800000600000800000600000600000400000c00000a00000a00000800000a00000800000800000600000a00000800000800000600000800000600000600000400000a000008000008000006000008000006000006000004000008000006000006000004000006000004000004000002 0x9000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009 512 576)) 0x100010117 0x8000000000000000 (N (N (N (N (N (N (N (N (N (fl 0xa0604) (fl 0x14130b)) (N (fl 0xe0706) (fl 0x332322))) (N (N (fl 0xd0a06) (fl 0x242212)) (N (fl 0x271307) e0))) (N (N (N (fl 0x22120a) (fl 0x251d0d)) (N (fl 0x261506) (fl 0x392923))) (N (N (fl 0x220804) (fl 0x191715)) (N (fl 0x220e0a) e0)))) (N (N (N (N (fl 0x220a06) (fl 0x150e0d)) (N (fl 0x2a0a06) (fl 0x333122))) (N (N (fl 0xc0604) (fl 0x311713)) (N (fl 0x1a0b0a) e0))) (N (N (N (fl 0x311913) (fl 0x221412)) (N (fl 0xc0b07) (fl 0x312a29))) (N (N (fl 0x161204) (fl 0x311a19)) (N (fl 0x2d290a) e0))))) (N (N (N (N (N (fl 0x130b04) (fl 0x231b0b)) (N (fl 0x120806) (fl 0x352522))) (N (N (fl 0x19130b) (fl 0x311413)) (N (fl 0x242307) e0))) (N (N (N (fl 0x151312) (fl 0x161312)) (N (fl 0x2d2506) (fl 0x312725))) (N (N (fl 0x140b04) (fl 0x311d15)) (N (fl 0x2a190a) e0)))) (N (N (N (N (fl 0x250d07) (fl 0x16150d)) (N (fl 0x220e06) (fl 0x2d2523))) (N (N (fl 0x140704) (fl 0x272313)) (N (fl 0x290c0a) e0))) (N (N (N (fl 0x292523) (fl 0x221612)) (N (fl 0x270d07) e0)) (N (N (fl 0x221404) (fl 0x323119)) (N (fl 0x1b0d0b) e0)))))) (N (N (N (N (N (N (fl 0x130704) (fl 0x1a190b)) (N (fl 0x260706) (fl 0x272522))) (N (N (fl 0x151307) (fl 0x393112)) (N (fl 0x271507) e0))) (N (N (N (fl 0x23130b) (fl 0x35250d)) (N (fl 0x242206) (fl 0x393123))) (N (N (fl 0x1a0a04) (fl 0x1b1915)) (N (fl 0x2a120a) e0)))) (N (N (N (N (fl 0x251506) (fl 0x150f0d)) (N (fl 0x260d06) (fl 0x292423))) (N (N (fl 0x240604) (fl 0x391913)) (N (fl 0xd0c0a) e0))) (N (N (N (fl 0x312322) (fl 0x1d1512)) (N (fl 0x2b0b07) (fl 0x333129))) (N (N (fl 0x171304) (fl 0x311d19)) (N (fl 0x190c0b) e0))))) (N (N (N (N (N (fl 0xd0706) (fl 0x33230b)) (N (fl 0xc0a06) (fl 0x2d2922))) (N (N (fl 0x312212) (fl 0x331513)) (N (fl 0x2d2507) e0))) (N (N (N (fl 0x311512) (fl 0x321312)) (N (fl 0x130807) (fl 0x392925))) (N (N (fl 0x120c04) (fl 0x323115)) (N (fl 0x24220a) e0)))) (N (N (N (N (fl 0x190b0a) (fl 0x1a190d)) (N (fl 0x261206) (fl 0x312723))) (N (N (fl 0xa0804) (fl 0x393113)) (N (fl 0x2a0d0a) e0))) (N (N (N (fl 0x70604) (fl 0x321912)) (N (fl 0x230f07) e0)) (N (N (fl 0x322204) (fl 0x272322)) (N (fl 0x130f0b) e0))))))) (N (N (N (N (N (N (N (fl 0x220604) (fl 0x2b130b)) (N (fl 0x160706) (fl 0x292422))) (N (N (fl 0x252206) (fl 0x2a2212)) (N (fl 0x161507) e0))) (N (N (N (fl 0x190d0b) (fl 0x26250d)) (N (fl 0x221606) (fl 0x323123))) (N (N (fl 0xe0a04) (fl 0x311715)) (N (fl 0x14120a) e0)))) (N (N (N (N (fl 0x250d06) (fl 0x250e0d)) (N (fl 0x160d06) (fl 0x393122))) (N (N (fl 0x140604) (fl 0x1d1913)) (N (fl 0x2a0b0a) e0))) (N (N (N (fl 0x252322) (fl 0x171512)) (N (fl 0x1b0b07) (fl 0x312d29))) (N (N (fl 0x241204) (fl 0x311b19)) (N (fl 0xd0c0b) e0))))) (N (N (N (N (N (fl 0x221204) (fl 0x24230b)) (N (fl 0x220806) (fl 0x312622))) (N (N (fl 0x19150d) (fl 0x1b1513)) (N (fl 0x332307) e0))) (N (N (N (fl 0x311312) (fl 0x1a1312)) (N (fl 0xb0807) (fl 0x2b2925))) (N (N (fl 0x240b04) (fl 0x272515)) (N (fl 0x221a0a) e0)))) (N (N (N (N (fl 0x251507) (fl 0x2d150d)) (N (fl 0x141206) (fl 0x352523))) (N (N (fl 0x240704) (fl 0x323113)) (N (fl 0x1a0d0a) e0))) (N (N (N (fl 0x312923) (fl 0x1b1912)) (N (fl 0x130f07) e0)) (N (N (fl 0x262204) (fl 0x353119)) (N (fl 0x2b0d0b) e0)))))) (N (N (N (N (N (N (fl 0x120a04) (fl 0x2b190b)) (N (fl 0xa0806) (fl 0x2d2522))) (N (N (fl 0x19120a) (fl 0x191413)) (N (fl 0x231707) e0))) (N (N (N (fl 0x25150d) (fl 0x2b290d)) (N (fl 0x322206) (fl 0x312625))) (N (N (fl 0x2a0a04) (fl 0x391915)) (N (fl 0x1b190a) e0)))) (N (N (N (N (fl 0x230b07) (fl 0x250f0d)) (N (fl 0x120e06) (fl 0x262523))) (N (N (fl 0xc0704) (fl 0x311b13)) (N (fl 0x190c0a) e0))) (N (N (N (fl 0x312522) (fl 0x351512)) (N (fl 0x170d07) e0)) (N (N (fl 0x241304) (fl 0x2b2919)) (N (fl 0x290c0b) e0))))) (N (N (N (N (N (fl 0x250706) (fl 0x2d290b)) (N (fl 0x1a0a06) (fl 0x392922))) (N (N (fl 0x312515) (fl 0x191713)) (N (fl 0xe0b0a) e0))) (N (N (N (fl 0x191513) (fl 0x151412)) (N (fl 0x230807) (fl 0x333125))) (N (N (fl 0x220c04) (fl 0x393115)) (N (fl 0x32220a) e0)))) (N (N (N (N (fl 0x190d0a) (fl 0x2d190d)) (N (fl 0x171506) (fl 0x2d2923))) (N (N (fl 0x120804) (fl 0x251615)) (N (fl 0x120e0a) e0))) (N (N (N (fl 0x131204) (fl 0x221a12)) (N (fl 0x141307) e0)) (N (N (fl 0x2b2304) (fl 0x2b2322)) (N (fl 0x230f0b) e0)))))))) (N (N (N (N (N (N (N (N (fl 0x120604) (fl 0x17130b)) (N (fl 0xf0706) (fl 0x252422))) (N (N (fl 0x151206) (fl 0x262212)) (N (fl 0x331307) e0))) (N (N (N (fl 0x29190a) (fl 0x291d0d)) (N (fl 0x351506) (fl 0x312b23))) (N (N (fl 0x230804) (fl 0x251715)) (N (fl 0x290e0a) e0)))) (N (N (N (N (fl 0x150d06) (fl 0x190e0d)) (N (fl 0xf0d06) (fl 0x353122))) (N (N (fl 0xe0604) (fl 0x1a1913)) (N (fl 0x1b0b0a) e0))) (N (N (N (fl 0x311915) (fl 0x311412)) (N (fl 0x170b07) (fl 0x312b29))) (N (N (fl 0x1a1204) (fl 0x291b19)) (N (fl 0x39290a) e0))))) (N (N (N (N (N (fl 0x230b04) (fl 0x291b0b)) (N (fl 0x150806) (fl 0x292622))) (N (N (fl 0x29230b) (fl 0x161513)) (N (fl 0x2b2307) e0))) (N (N (N (fl 0x191312) (fl 0x171312)) (N (fl 0x352506) (fl 0x2a2925))) (N (N (fl 0x1b0b04) (fl 0x262515)) (N (fl 0x39190a) e0)))) (N (N (N (N (fl 0x231307) (fl 0x17150d)) (N (fl 0x250e06) (fl 0x332523))) (N (N (fl 0x170704) (fl 0x2b2313)) (N (fl 0xf0d0a) e0))) (N (N (N (fl 0x312523) (fl 0x311612)) (N (fl 0x2d0d07) e0)) (N (N (fl 0x231404) (fl 0x333119)) (N (fl 0x1d0d0b) e0)))))) (N (N (N (N (N (N (fl 0x230704) (fl 0x1d190b)) (N (fl 0x270706) (fl 0x2a2522))) (N (N (fl 0x252307) (fl 0x151413)) (N (fl 0x351507) e0))) (N (N (N (fl 0x29190b) (fl 0x2a290d)) (N (fl 0x2a2206) (fl 0x292625))) (N (N (fl 0x240a04) (fl 0x351915)) (N (fl 0x32120a) e0)))) (N (N (N (N (fl 0x130b07) (fl 0x190f0d)) (N (fl 0x2d0d06) (fl 0x312423))) (N (N (fl 0x260604) (fl 0x231b13)) (N (fl 0x120c0a) e0))) (N (N (N (fl 0x292522) (fl 0x321512)) (N (fl 0xe0d07) (fl 0x353129))) (N (N (fl 0x1b1304) (fl 0x2a2919)) (N (fl 0x230c0b) e0))))) (N (N (N (N (N (fl 0x150706) (fl 0x2a290b)) (N (fl 0x160a06) (fl 0x322922))) (N (N (fl 0x312313) (fl 0x351513)) (N (fl 0x352507) e0))) (N (N (N (fl 0x311912) (fl 0x331312)) (N (fl 0x150807) (fl 0x312d25))) (N (N (fl 0x130c04) (fl 0x333115)) (N (fl 0x26220a) e0)))) (N (N (N (N (fl 0x290b0a) (fl 0x1b190d)) (N (fl 0x321206) (fl 0x2a2923))) (N (N (fl 0xb0804) (fl 0x191615)) (N (fl 0x2d0d0a) e0))) (N (N (N (fl 0xb0a04) (fl 0x391912)) (N (fl 0x250f07) e0)) (N (N (fl 0x272304) (fl 0x2a2322)) (N (fl 0x190f0b) e0))))))) (N (N (N (N (N (N (N (fl 0xb0704) (fl 0x33130b)) (N (fl 0x170706) (fl 0x312422))) (N (N (fl 0xd0b07) (fl 0x353112)) (N (fl 0x1d1507) e0))) (N (N (N (fl 0x290d0b) (fl 0x27250d)) (N (fl 0x251606) (fl 0x353123))) (N (N (fl 0x140a04) (fl 0x1a1915)) (N (fl 0x16120a) e0)))) (N (N (N (N (fl 0x221206) (fl 0x290e0d)) (N (fl 0x1d0d06) (fl 0x252423))) (N (N (fl 0x160604) (fl 0x331913)) (N (fl 0x2b0b0a) e0))) (N (N (N (fl 0x292322) (fl 0x1a1512)) (N (fl 0x270b07) (fl 0x323129))) (N (N (fl 0x321204) (fl 0x291d19)) (N (fl 0x130c0b) e0))))) (N (N (N (N (N (fl 0x231304) (fl 0x27230b)) (N (fl 0x250806) (fl 0x2b2922))) (N (N (fl 0x29250d) (fl 0x1d1513)) (N (fl 0x262507) e0))) (N (N (N (fl 0x191512) (fl 0x1b1312)) (N (fl 0xd0807) (fl 0x352925))) (N (N (fl 0x2b0b04) (fl 0x2d2515)) (N (fl 0x291a0a) e0)))) (N (N (N (N (fl 0xd0b0a) (fl 0x35150d)) (N (fl 0x1a1206) (fl 0x292723))) (N (N (fl 0x270704) (fl 0x353113)) (N (fl 0x1d0d0a) e0))) (N (N (N (fl 0x312925) (fl 0x1d1912)) (N (fl 0x150f07) e0)) (N (N (fl 0x2a2204) (fl 0x262322)) (N (fl 0x2d0d0b) e0)))))) (N (N (N (N (N (N (fl 0x220a04) (fl 0x39190b)) (N (fl 0xd0806) (fl 0x322522))) (N (N (fl 0x29220a) (fl 0x231413)) (N (fl 0x251707) e0))) (N (N (N (fl 0x29190d) (fl 0x39290d)) (N (fl 0x272506) (fl 0x292725))) (N (N (fl 0xf0b04) (fl 0x251d15)) (N (fl 0x1d190a) e0)))) (N (N (N (N (fl 0x150d07) (fl 0x290f0d)) (N (fl 0x150e06) (fl 0x2b2523))) (N (N (fl 0xf0704) (fl 0x242313)) (N (fl 0x220c0a) e0))) (N (N (N (fl 0x312922) (fl 0x191612)) (N (fl 0x1d0d07) e0)) (N (N (fl 0x331304) (fl 0x2d2919)) (N (fl 0xe0d0b) e0))))) (N (N (N (N (N (fl 0x120a06) (fl 0x39290b)) (N (fl 0x260a06) (fl 0x312a22))) (N (N (fl 0x312919) (fl 0x231713)) (N (fl 0xf0b0a) e0))) (N (N (N (fl 0x311513) (fl 0x191412)) (N (fl 0x250807) (fl 0x393125))) (N (N (fl 0x230c04) (fl 0x291a19)) (N (fl 0x2b290a) e0)))) (N (N (N (N (fl 0x290d0a) (fl 0x39190d)) (N (fl 0x1d1506) (fl 0x332923))) (N (N (fl 0x130804) (fl 0x311615)) (N (fl 0x190e0a) e0))) (N (N (N (fl 0x232204) (fl 0x311a12)) (N (fl 0x1b1307) e0)) (N (N (fl 0x332304) (fl 0x322322)) (N (fl 0x290f0b) e0))))))))) (C 12 (C 10 (C 6 (C 9 (C 5 (C 3 (C 36 (C 40 (C 24 (C 34 (C 20 (C 18 (C 38 (C 50 (C 33 (C 17 (C 48 (M 2 0x246650012c550024a4d00268390026235002702d0021eb20021eaa0021ea60021e720021e6a0011e5a0011e560021e1e) (M 2 0x170d100170c500168c5002608d0016065002605900160550024a4d00260390026035002602d0021eb20021eaa0021ea60021e720021e6a0011e660011e560021e1e)) (M 2 0x2684500258450025445002384500234450012c450012c390026235002702d001221d0021ea60021e960021e8e0061e460011e3a0011e1e00204ff00204e700204c7)) (M 3 0x1629500270850026885003588500354850034271003426900142650034259003424d002622d003421d0091e860021e660031e560031e3a0033e360013e2e001064b0010647003063f004013300205070030503)) (M 2 0x170c900268c500264b100264a5002649500264710016469002646500264590026455002644d0017045002642d002641d0021eaa0021e8e0011e6a0051e460021e3a0025e360060643)) (M 4 0x464a900368a50047099004629900458990036095004608d00168850044c710044c69003606500142650044c590044c550044c4d0044235004422d0044c1d00c1e9a00c1e460041e3a001063f001062b)) (C 17 (C 33 (M 2 0x168490026249002544900252490014c490024a49002384900232490022a4900264390016835002702d0021eb20011e9a0021e8e0061e4a0015e360021e1e002055b00205430020523) (M 2 0x242590014c4d00168490025849002544900252490014c490024a490024249002384900232490022a490024235002422d002421d0061e860061e4a0021e3a001056f002056b002055b0010523)) (M 2 0x1684500252450024c450014a450024645002384500424450016835002222d002221d0021eb20021eaa0011e960061e460015e3a0011e3a0011e3600604c300204b700204b300600ab00204af00204ab00204a700204a3))) (C 18 (C 17 (C 33 (M 2 0x158550017051002645100262510015851002545100252510023451002284d0022835002322d002681d0021e9a0021e960021e8e0061e520021e3a00105bb00205a3002058b001057f) (M 2 0x242590014c5500164510025851002545100252510014c510024651002425100234510023251002284d0024235002422d002421d0061e860061e520021e3a00105b700205b300205a3001057f)) (M 2 0x27045002644500258450024a45002344500228390022235002221d0021eaa0011ea60021e9a0011e860061e460021e2e001050b002050300204e300204db00204d700600b300204d300204cf00204cb00204bb)) (W 0x1425100162490015849001544900152490014c490014a4900132490012835001702d001241d0011e8e0021e860031e4a0011e3a0010537001053300300bf001052f001052b0010527001051700300a3))) (C 33 (C 18 (C 48 (C 17 (M 2 0x262990027089001588900252890024a89002446500244590024455001585100254510024651002444d00144390026835002642d0061e8a0021e720021e6a0011e520013e3a0021e1e) (M 2 0x244550014a4d00168450025845002544500252450024c450014a450024445002384500234450022c450027035002442d002441d0061e8a0061e460021e3a00104db00204d700204cf00104bb)) (W 0x1588900152890014471001446900144650014459001445500160450014a4500144450016039001602d001441d0031e8a0021e520011e4e0011e360010693001068f002068b00106870010673001065700105b7)) (M 2 0x27049002584900252490024a490013849002324900124390013835002442d002241d0061e8a0061e4a0011e3a0011e36006013700205670020563002055f0020557002053f00205370020533002051f00204b300204a300200a3)) (W 0x1588900170850016885002448500142590014455001465100144510013251001424d00342450014235001422d001421d0031e860011e720011e6a0011e4a0011e3a001060300405ff00300d300105fb00105f700105f300105ef002055f))) (C 18 (C 17 (C 33 (C 20 (C 34 (M 2 0x26861002646100262610024a61002466100230590023055001304d0027035001522d001302d0014c1d001261d0021eb20021eaa0011ea60011e9a0061e620021e3a00205d300205cb00205c3) (M 2 0x1386900138650013465002586100252610024c610024a61002466100244610014459001305900144550013055001444d001304d0026235002442d002441d0061e8a0061e620021e3a002068700205eb00205e7)) (M 2 0x24a6100262510025851002545100252510024c510024651002284d0022835002302d001441d0051e8a0061e520015e3a0011e3a0011e1e002059b002059700600c70020593002058f00205830020577)) (M 2 0x1688500264850024271002586100254610024c61002466100642610023059002305500472510014251002304d0024235002422d002421d0061e860061e620021e3a002064b00205ff00205f700205ef00105eb00105cb00205c30010593)) (M 3 0x368610036461003584500352450034c450034a4500344450032c4500330390032235003222d0021eaa0051e8a0021e860091e460031e1e00105fb003050300304fb00304f700304f300900b700304ef00304eb00304df00900af00304bf)) (M 2 0x2626100268490025849002544900252490024a49001464900142490022a4900224390023035002242d0011e8a0051e860061e4a0021e1e0020563001055f00205570020553002054f00600c3002054b0020547002053b00600bb002051b00600a7))) (C 34 (C 33 (C 48 (C 24 (C 18 (C 20 (M 4 0x258a900258a500254a500468a100464a100462a100250990024c95002508d0024a8d00450590045055004504d0023845004344500250350023835004702d001221d00c1ea20041e660051e460033e3a0011e3a0031e1e) (M 2 0x14a590025055002645100162510025451002525100250510014a51002465100234510023251002284d0025035002502d0024c1d0061ea20061e520021e3a00204db00104d700204d300104cb)) (M 2 0x250590025055004504d0025849002524900250490024c490024a4900246490023849002324900324450025035002502d002241d0061ea20061e4a0021e3a00205370020533001052b001051700204b300104af)) (M 2 0x262610024c610024a6100246610025055006304500230390023035002302d0061ea20061e620021e1e00205df00205db00205d700205cf00205c700805bf001059b002059700205830010553002054f00100bb002051b)) (M 2 0x860a100260990026095002608d00138690025065006604500250390025035002502d0061ea20011e720011e6a0021e560021e4e0021e1e00206d700206d300806cf00206cb00206c700206c3006013f00405bb002058b0060573)) (M 3 0x378d50035099003688500264850034271003426900342650034259003505500650510034251003504d0035049001424900942450034235003422d003421d0091e860051e620041e4a0031e3a003063b00c063700900df0030633003062f0030627003060b00305d7001054f)) (M 3 0x362a1002688900650890034a890034471003446900344650035059003445500350510014451003444d00944490035035003442d003281d0091e8a0011e520081e460031e3a003068300c067f00900eb003067b0030677003066f003065300900cf00905db00104db))) (C 20 (C 33 (C 34 (C 17 (C 18 (C 24 (C 40 (M 2 0x27091001649100254910025291002488d00248650014a5900148590024855002484d002622d002681d0061e920021e720021e6a0021e3a0023e3600106bb00206b700206a3001069b) (M 2 0x26291001488d002486500146590025055002484d0024835002502d001481d0061e920021e720021e6a0011e5a0021e3a0013e1e00206b300206af00600ef00206ab00206a7002069f0020697)) (M 2 0x262910013465002546100252610024c610024a610024861002466100230590023055001484d001304d00248390024835002481d0061e920061e620021e2e00206bf00205eb00205e700205df00205cf00105c700105bf)) (M 2 0x25491002488d00448690024855002484d00270490026249002584900252490024a4900248490023849002324900230490024835002502d002241d0061e920061e4a0021e3a00106bb00206af002069f001054f00300c30020543)) (M 3 0x35091003488d003486900348650034861006484d0012a4d003484900364450065845003544500352450034c45003484500338450022c45005244500348390034835003222d0091e920091e460031e1e00300ef00306970030513003050f00304f300204df00104bf00104a7)) (M 2 0x2708900262890025289002447100248690024c61002486100244590024455001324d0064449002484500230390024835002441d0061e8a0011e660011e4e0041e460021e2e002066b008066700600e70020663002065f00600e3002065b002064f)) (M 2 0x170c9001649100170850025485002488500242710024269002486500248610014261002425900242550014849002424900248390024235002421d0061e860031e620031e4a0021e2e0020623002061f00600db002061b002061700600d70020613002060700600cb004050700204c3)) (W 0x170510016451001625100248510014651001345100132510033051001284d0032849003284500148390014835001481d0031e920031e520011e2e00106a7001065f00200e30030623003013b00105af00105ab00105a7004059f0040587004057b))) (C 18 (C 34 (C 33 (C 17 (C 36 (C 40 (C 20 (M 6 0x660650016061003586100654610014a610054661001465900358550054a4d0053839001343900360350032a35005622d001262d006641d007700d006680d006600d006520d0064c0d005340d0052c0d0125e0e0123e0e0061e0e00105e300105d3) (M 2 0x2585100252510024a51002465100228390022835002262d002621d002700d002680d002640d002540d0024c0d002280d0065e0e0063e0e0021e0e00205a300100c70020593002058f002058b001057f0010577)) (M 2 0x262a1002509900250710025069002505900250550024651002504d00228390025035002642d002661d002700d002680d004600d002500d0024a0d002320d002280d0065e0e0063e0e0021e0e00106c7001013f00205df00105db00205d7)) (C 20 (M 2 0x264910024871002486900248650024a6100246610024855002484d00248390024835002662d002621d002700d002680d004600d001520d001500d002480d002300d0022c0d0065e0e0063e0e0021e0e00206b700206ab00106a7002069f) (W 0x34851001484d00128390012835001462d001621d001700d001680d001640d001480d001340d001280d0035e0e0033e0e0011e0e00106af00106ab00106a7003013b00105af00105ab00105a7001059f0020597001058f0010587001057b))) (M 3 0x358450035645003544500350450034e450034c450034845001503900248390032235003700d003680d003640d002520d004500d0034a0d003480d003340d0032c0d003220d0095e0e0093e0e0031e0e00106a700304ef00900b300604bf00301cf00301cb00301c700301c300301b3003017b)) (W 0x36085002508500142710014269001586100150610014261001425900142510014235002700d001680d001640d001540d0014c0d001420d001320d001280d0011e3a0035e0e0033e0e0020607001057b00401f300301ef00101eb00101e3003002b00101bb0010183)) (M 2 0x66089001588900244710024a6100244610044455002445100134390015835002700d002680d002620d002520d00a440d001340d001320d002280d006220d0065e0e0063e0e0021e0e0060653006064f002058300801ff00201fb00201f700600ff00801e700201bf0020187)) (W 0x15849001524900350490014a49003484900124390013835002740d0026c0d001600d001540d0014c0d003420d001320d0012a0d004240d0035e0e0033e0e0011e0e0010573001056b0010537003051b002051700101df00401db003002f00101d700101d300300fb00101b7))) (C 17 (C 20 (C 3 (C 36 (C 33 (C 40 (C 34 (C 18 (M 6 0x358a900660650064a6100260590064655004304d00634390066035003542d003522d006621d006701500668150066415003581500352150064c15002381500430150042c1500226150125e160123e160061e1600405d3) (M 2 0x2544900252490024a49002464900224390022a35002242d002621d00270150026815002641500258150024c1500224150065e160063e160021e16002055b00100c3002054b00205470010543001053b0020523)) (M 6 0x55889006447100644650054a610064461008445d006445900152550014a550044455005444d001344d0014439005343900168350056235006442d006701500568150066415001581500552150064415006301500e24150061e1e0125e160123e16004068700606730060657001056b002056700100c3)) (C 18 (C 24 (M 2 0x25069002506500250550024a4d00250390026035002502d002621d00270150016815002641500160150025015002461500238150022c150065e160063e160021e1600106d700206c7002067b0020677002066f) (M 2 0x146550014455002304d0023039002502d002621d0027015002681500264150025015002441500230150022c150065e160063e160021e16002066f0010653006013f00205df00205db00205d700205cf00205c700205bf)) (M 3 0x262a1003505500460490035849003524900350490034c490014a4900346490033849003324900350390036035003502d001621d0024a1d00370150036815007641500350150014415003301500324150095e160093e160031e1600105c70030567002055700200c3003053b003051f))) (W 0x14269001426100142490015439001422d00170150016815001641500158150014c15008421500132150012c150035e160033e160011e16003062b003062700305ef001054b001051b001029b00102970010293001028b0010263001022b)) (W 0x1487100248690014865001485900130490014839001262d00164150016215001521500748150014615001301500124150035e160033e160011e1600106ab003069b0020697003065b001055300102a700102a3001029f003010b001028f0010267001022f)) (M 2 0x2546900256650015861002643900466150026215002521500138150013015002700d002680d006600d004500d0024c0d002300d0022c0d0100a0d0065e0e0063e0e0021e0e00105df00105cf006022f0060187006017f00201570020153006000b002014f002014b00201470020143)) (W 0x15451001505100144510012839001342d00170150016415001621500158150014c15001321500b281500126150030a0d0035e160033e160011e1600106770010653003057f00305770030527003028b001028700102830030053001027f001027b001025f0040227)) (M 2 0x254450025045002444500150390014439002222d00270150026815002641500252150024c15005481500238150022c1500e22150065e160063e160021e16001067b002065300604e700604df00204af00404a300102a300202770070273006004f002026f0060107002026b002025b00202230060007))) (C 3 (C 24 (C 33 (C 17 (C 40 (C 5 (C 36 (C 20 (C 18 (M 4 0x460a900444650014a5900244590045255004444d00358390012c390047235004702d004682500464250026225006602500158250034a250044625004382500434250044c1d00c5e2600c3e260041e26002068b) (M 2 0x252490024c490024a4900246490022a4900224390026235002702d00268250026425002602500258250015425001442500238250022425002601d0065e260063e260021e26001056700205570020543002051f)) (M 4 0x2446500462510045851004545100452510044c5100446510023451004284d002443900228390046035002702d002322d00170250046825004642500360250044a25004442500428250022425004441d00c5e2600c3e260041e2600105bb004058b004052f002052b0040527)) (C 34 (M 2 0x1488d00248710024869002486500146590024855002484d0025249002484900248390026235002702d0026825002642500260250025425002482500228250022425001481d001281d0065e260063e260021e2600206b700206a300205a70010587) (M 2 0x244650024455002444d006444900244390026235002702500248250024425001382500234250012825002441d0021e2e0065e260063e26002066b008066700600e70020663002065f002065b002064f00205ab001059f0020587))) (M 5 0x356490054c490055439005682500a6025008442500526250057215005701500564150036215002601500558150044615001441500538150052c15019121500f5e1600f3e160051e160010657002056b005055700f026700f025f0050243005023f005023b00502370050233005021b)) (M 3 0x3506d0035059001505500552510035051003504d0035049003503900368250036425003622500850250034a2500346250033825002342500424250022a1d001241d00912150095e260093e260031e2600606c3003069f00300eb00600e3001052b00303c700303c300303bf00303af00c03870030363)) (W 0x25a4500154450014c45001484500244450014439001662500164250014a2500248250014625001382500134250072225001221d0035e260033e260011e26001050f00204ff00304cf00204ab00104a700103c700103c300103af00103970010393001038f001038b001037b0010357003003f)) (M 2 0x660850024275004426d00248510024251002284d00242490022c3900270250046825002642500258250025425002382500234250022a250042425002421d0065e260063e260021e26001061300205f700105f300300cb00803bb006011f00203b700203b300203ab00600830020383002035f0060043)) (W 0x14c610014a610014861001466100144610013039001642500162250015425001482500930250012a250012625001441d00312150035e260033e260011e26001066300305c30010597002058f0020547001053b00303ab00103a700103a30030087001039f001039b003011b004037f001035b)) (M 2 0x2605500258510024c510024839002642500460250065025002482500238250063025002720d002700d002680d002620d002540d0014a0d001480d002340d0022c0d00a120d0065e0e0063e0e0021e0e00105a700601bf00601b7008019b0020197006001f0080193002018f006001b002018b00201730060003))) (C 34 (C 18 (C 5 (C 36 (C 20 (C 3 (C 9 (C 40 (C 33 (C 24 (M 2 0x146690025459002325500252450024c450014645001344500260390026035002642d002681d00270190026219002601900258190024a19002381900226190065e1a0063e1a0021e1a) (M 2 0x2546100252610024c61002465900260390023035002302d002641d002701900168190026219001601900258190024a19002301900226190065e1a0063e1a0021e1a00105eb00205c300204ef00204eb00204df)) (M 2 0x25485002427100242690024c610024261002425d00242590024255002424d00264390024235002322d00270190026819002621900258190024219002301900422190021e1e0065e1a0063e1a002063f002062b001060f00101330010503)) (C 24 (M 2 0x264a10025071002466500250590025055002504d00250450024c4500268390025035002502d0026c1d00270190026219004601900250190014a190014219002341900222190065e1a0063e1a0021e1a00206c30020633002062f0010627) (W 0x164610014c61001505900230450013035001302d001621d001701900168190015019001421900130190012a190011e3a0035e1a0033e1a0010627001060b003013f00105df00105db00105d700105cf00105c700305bf00104bf))) (C 17 (C 24 (C 33 (C 40 (M 2 0x14659001524d0014c4d0015235002322d00268250026425002602500254250014a250023825002601d00270190026219002601900258190014a19001461900234190022a190065e1a0063e1a0021e1a) (M 2 0x250590024a25002462500234250022a250024c1d0016419002621900160190025019002381900226190065e1a0063e1a0021e1a00206d700106d300206c300203c700203c300203bf00203af00203870020363)) (M 2 0x2424d0024c390025825002542500234250022a250022c1d002701900164190016019002421900238190065e1a0063e1a0021e1a00206470010643002063f00203bb006011f00203b700203b300203ab0020383002035f)) (W 0x14c6100164390015825001462500342250012a2500126250012c1d0016219001601900154190014a1900130190035e1a0033e1a0011e1a00105eb00105c300103a700403a30030087001039f001039b001037f001035b)) (W 0x14c450012c3900168250016425001602500154250014a2500138250013425001601d001701900160190015019001461900122190035e1a0033e1a0011e1a00103c300103af001039700103930030083003011b001038f001038b001037b0010357))) (M 3 0x5506d0016461003586100332350036219007601900350190033819003700d0046c0d002680d002640d001600d003540d0034a0d003340d005300d0032a0d0150c0d0095e0e0093e0e0031e0e00106d7003019b0090183009017b0060173003016f003016b00301670030163003015f003015b)) (M 3 0x142650035c510035851003545100352510034a510012835002502d001322d0022825003701900364190036219006501900342190033419018281900326190090c0d0095e1a0093e1a0031e1a009058b009058300904cb00303b300103af002038300303170030313003030f003030b00302ef00c02b7)) (M 2 0x6609100650910064885002487900248650024861002484d00248450012a35002522d002482500270190026419002621900254190024619002381900234190012a1900122190040c0d0065e1a0063e1a0021e1a003011b001037f00803370080333008032f002031f006006b00202f700602bf002016f)) (M 2 0x150710045061002522d002681d0026219002601900254190023419006701500264150026015002581500246150013815001321500226150120c150065e160063e160021e16001013f00105c3006022b0060223006021b00202170020213006003b002020f002020b00600370020207002020300600f3)) (M 4 0x4524900450490074e490014a490044249002542d002502d0034a25004242500470190046819004621900458190044619007421900438190042a19028241900c0c1500c5e1a00c3e1a0041e1a001062f00c054300c053b00404ab00804a700103bf004038700c031f0040307004030300402ff00c011300402fb00402eb01002b300c0013)) (M 6 0x1260890055289006446900644650034c4d00f4445003303500144250032a25006701900668190096619006621900658190064a190454419002381900430190032a1900326190125e1a0123e1a0061e1a012066f01205f3004039f003037b006035b018032b006032701201170060323006031b0120313012006700602f300602bb01202170120017))) (C 24 (C 34 (C 9 (C 6 (C 18 (C 40 (C 3 (C 5 (C 36 (C 33 (C 48 (C 20 (M 2 0x2464d0024c450024a45002384500170350015235001642d001542d00170290026829001642900262290025829001522900232290022c290022a1d0065e2a0063e2a0021e2a) (W 0x154510014c510014a5100146510012835001642d0017029001682900162290015829001522900128290012629001281d0035e2a0033e2a0011e2a00104d300104cf00104cb)) (M 2 0x24c690022c55002604d002544500252450024a4500260390026035002602d00268290026229002602900258290024629001382900232290012829002601d0065e2a0063e2a0021e2a00205bb00205b700105a3)) (M 2 0x158850014c85002427100242690024265002425900254510024251002424d002643900142350012a35002702d00268290026229002602900158290014c29002422900228290022229001601d001421d0065e2a0063e2a0021e2a001063f002060f001050b002050700104e3)) (C 20 (M 8 0xe609100748710014869008486500848590054855008484d001564500854450034845001643900734390084835007642d001522d0087029016682900862290084829008462900138290082229008481d0185e2a0183e2a0081e2a008069b008061b0070617008061300204e700104e3) (M 2 0x45c5100254510022835002642d0027029002622900648290014629001422900228290022229002281d0021e3a0065e2a0063e2a002062300206170010607006013b00205af00205ab00205a7002059f0020587002057b00204cf00204bb))) (C 17 (C 20 (C 33 (C 36 (M 2 0x14655001544d0014a4d00154390012a35002342d00268290026229002602900252290014c290023829002601d00270150026415002601500258150014c15001461500132150022c150065e160063e160021e16) (W 0x1542d00162290016029001482900132290012c2900170150016415001601500152150014615001381500126150035e160033e160011e16001069b00102a700102a3001029f001028f0010267001022f)) (W 0x1424d0015439001342d001422900138290016815001641500158150014c15001421500132150012c150035e160033e160011e16001064b002062b001029b0010297003010b0010293001028b0010263001022b)) (W 0x15439001342d0014629001282900170150016415001621500158150014c150013215004281500126150035e160033e160011e16003057f0010297002028b001028700102830030053001027f001027b001025f0010227)) (W 0x1343900152290014c2900122290017015001681500164150015815001461500138150012c1500522150035e160033e160011e1600304e7003028f00102770010273003004f001026f0030107001026b001025b0010223))) (M 2 0x160910016071002485d00158510024c510022a350026429002622900260290015829001482900138290012829002740d002700d003680d002600d002520d002480d002320d0022c0d002280d008140d0060a0d0065e0e0063e0e0021e0e00201eb00401bb00601b300201af00201ab00201a700201a3002019f0080177)) (M 4 0xc60a100c50910095085008506d0025065004505900750550045051002504500450350046829004642900462290044c2900446290043829004262900822290032815008140d00c5e2a00c3e2a0041e2a010043f010043b00d0437004042700403ff00c03db0040283002026f003022b00401af)) (M 2 0x26249004564900252490024c490024a490012a3500270290026829002582900246290044229002382900232290162429002481d00224150065e2a0063e2a0021e2a006055b006052b00604af0060427002040f002040b0020407002040300203f300203cf002010b001028f00102670060023)) (M 2 0x168950014a55001465500252450024235001682900560290024229002322900374190027019002641900262190025819001461900142190023819002221901614190065e1a0063e1a0021e1a00104c700104c300603ff00602f700602ef00202d300202cf00202cb00202c7006005700202c300202ab0060207006000f)) (M 4 0x1705100358510044c51003702900462290056029004482900238290022c2900c242900474250046825004642500460250014a250034825004462500c422500238250022825004262500822250042a1d00c141900c121500c5e2600c3e260041e26003069b00205870040357004034f010034b00c0077010034700c0343010033f010033b00c00f7)) (M 2 0x16295001447100244590024455004545100244450014a350012235002702900162290025829002522901444290022829001262900122290061425002681d0024415001381500126150065e2a0063e2a0021e2a0060687006065f00605fb00204330060127002042f002042b0020423006009300203fb00803d7006005b002026f0060027)) (M 2 0x24269006606100252610024a610024861002466100248550063051006304500130350026829002642900262290024829002422900630290022c290022629006141900258150024c150013015004140d0065e2a0063e2a0021e2a0060423008041f002041b006009700804170080413006012300803f700603d3006007300102630020177))) (C 5 (C 36 (C 9 (C 10 (C 40 (C 20 (C 24 (C 6 (C 3 (C 34 (C 18 (C 17 (M 6 0x67085006688500254850024c7100242710014c5900658550014c4d002324d0032c4d006603900460350023835006643100662310066031004543100652310024c31004343100432310022c31004462d002342d0064a1d0125e320123e320061e32002060f) (M 2 0x2584500252450024c450024a45002464500234450026835002703100264310026231002543100242310022c310022231001602d001422d002221d0021e3a0065e320063e32001013300204fb00204e700204c7)) (M 8 0x6427100b60490025849006544900852490084c490084a490074649001424900832490026839006583900668350023835008703101364310086231002543100842310062a310082431008422d008241d0185e320183e320081e320080523001050300500ab00804af00804a700204a3)) (C 17 (C 18 (M 2 0x2447100244590024455002444d002683900270350026431002623100260310024a31002443100234310023231002442d002441d0065e320063e320021e320010673002065700100d300205fb00205f700105f3) (W 0x1584900132490012a490016839001383500164310016231001443100142310012431001442d001441d0035e320033e320011e3200105f700105ef003013700105670010563001055f0010557001053f001051f)) (M 2 0x2445900244550044449002544500252450024c450024a450024445005424500234450023839002583500268310066431006623100244310022231002442d002221d0065e320063e320021e32002065700105ff002051300204c700204ab))) (C 17 (C 18 (C 33 (C 34 (W 0x158550014a4d001383500164310016231001603100152310014c310013431001602d001461d001700d001680d001600d001540d001320d0012c0d0035e0e0033e0e0011e0e) (W 0x1583500162310016031001443100132310012c31001700d001680d001600d001520d0014a0d001340d0012a0d0035e0e0033e0e0011e0e001065700101ff00101fb00101f700101e700101bf0010187)) (W 0x142550015839001383500142310013431001680d001640d001540d0014c0d001420d001320d0012c0d0035e0e0033e0e0011e0e001064b002060f00101f300101ef00101eb00300ff00101e300101bb0010183)) (W 0x1583900138350014a310012431001700d001680d001620d001540d0014c0d001320d0012a0d004240d0035e0e0033e0e0011e0e003052300101ef00201e300101df00101db003002f00101d700101d300101b7001017f)) (W 0x1383900152310014c310012231001700d001680d001640d001540d0014a0d001340d0012c0d005220d0035e0e0033e0e0011e0e00304c700301e700101cf00101cb003002b00101c700101c300300fb00101b3001017b))) (M 4 0x4524500446450066c310046431004603100442310042a31004322d002701900468190046219006601900454190014a1900c4419003421900434190042619008181900c0c0d00c5e1a00c3e1a0041e1a002064b003050700c02eb00402e701002e300402df00402db00402d701002af)) (M 3 0x154a5003426d00154610034c610034a6100346610024461003426100630450036831003643100362310034431003423100f30310032c310032a31002522d001302d0091819005300d0095e320093e320031e3200905d3009054b00304bf003047f003047b0030477009047300c0457003044700101fb0030187)) (W 0x14c710014a710016051001545100152510024651001445100142510032849003284500164310016231001603100144310014231001343100132310012831001262d001421d001440d001280d0035e320033e320011e3200105bb002046f001046b003012b0040467004046300104530010443003005f)) (M 2 0x660a100550890065085001506500250590025055002504d004504900350450027431002723100268310026431002623100750310024c310024a3100234310022231002500d0065e320063e320021e320010653008049f007049b00804970020487006009f006046b002045f002044f00302e700202af00101c700201b7001016b)) (M 4 0x3606d0044255004683900460390047031004643100452310043231004622900460290044c29002462900242290042c2900c2429007222901c18290044a1d00c140d00c5e2a00c3e2a0041e2a001060f001050300404c300c045300c03fb00403ef00403eb00c008f00403e701003e300c008b00403df01003cb00c010f)) (M 2 0x15c690024c4d003564900260350026231002603100344310022c31006283100270250026825002642500254250024a25002462500144250022a25002242500c1825002441d0061819006120d0065e260063e260021e26001055b0060383006037b00203770020373006007f008036f002036b006007b00803670080353006006f)) (W 0x36091001628d003488900348850024875001486900148650014859003484d0014845001703100164310015431001523100448310012a31001243100222310031825001481d002240d0035e320033e320011e320040493003012f004048f004048b0010483003047b003009b001045b004044b00203ef00103cb0030063)) (W 0x1548d00160490014c4900144490016a31001623100160310035031001443100134310033031001262d003182900170150016815003641500160150015215001441500132150012c1500518150030a0d0035e160033e160011e160030263003025b00402570010253003004b004024f001024b003004700402470030103004021f0030033)))
def cp_27_3 : CertItem := CI (some (BV 0xf00000d00000d00000b00000d00000b00000b00000900000d00000b00000b00000900000b00000900000900000700000d00000b00000b00000900000b00000900000900000700000b00000900000900000700000900000700000700000500000d00000b00000b00000900000b00000900000900000700000b00000900000900000700000900000700000700000500000b000009000009000007000009000007000007000005000009000007000007000005000007000005000005000003 0x9000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009 576 576)) 1 0x8000000000000000 (N (N (N (N (N (N (N (N (fl 0x50302) (fl 0x232109)) (N (fl 0x60503) e0)) (N (N (fl 0x70502) e0) (N (fl 0x210705) e0))) (N (N (N (fl 0x110905) e0) (N (fl 0x210b03) e0)) (N (N (fl 0x110a02) e0) (N (fl 0x232105) e0)))) (N (N (N (N (fl 0x210902) (fl 0x232111)) (N (fl 0x110703) e0)) (N (N (fl 0x110602) e0) (N (fl 0x210d05) e0))) (N (N (N (fl 0x120302) e0) (N (fl 0x252103) e0)) (N (N (fl 0x232102) e0) (N (fl 0x210d09) e0))))) (N (N (N (N (N (fl 0x90502) (fl 0x211311)) (N (fl 0x150503) e0)) (N (N (fl 0x150502) e0) (N (fl 0x190905) e0))) (N (N (N (fl 0x60302) e0) (N (fl 0x231103) e0)) (N (N (fl 0x191102) e0) (N (fl 0x210a09) e0)))) (N (N (N (N (fl 0x210503) e0) (N (fl 0x130903) e0)) (N (N (fl 0x120902) e0) (N (fl 0x251105) e0))) (N (N (N (fl 0x50402) e0) (N (fl 0x110605) e0)) (N (N (fl 0x50403) e0) (N (fl 0x291109) e0)))))) (N (N (N (N (N (N (fl 0x110302) (fl 0x312109)) (N (fl 0xd0503) e0)) (N (N (fl 0xd0502) e0) (N (fl 0xb0905) e0))) (N (N (N (fl 0x211105) e0) (N (fl 0x151103) e0)) (N (N (fl 0x131102) e0) (N (fl 0x312105) e0)))) (N (N (N (N (fl 0x90503) (fl 0x292111)) (N (fl 0xa0903) e0)) (N (N (fl 0xb0902) e0) (N (fl 0x131105) e0))) (N (N (N (fl 0x220302) e0) (N (fl 0x312103) e0)) (N (N (fl 0x292102) e0) (N (fl 0x131109) e0))))) (N (N (N (N (N (fl 0x210502) (fl 0x211911)) (N (fl 0x250503) e0)) (N (N (fl 0x250502) e0) (N (fl 0x290905) e0))) (N (N (N (fl 0xa0302) e0) (N (fl 0x211303) e0)) (N (N (fl 0x311102) e0) (N (fl 0x210b09) e0)))) (N (N (N (N (fl 0x210903) e0) (N (fl 0x230903) e0)) (N (N (fl 0x220902) e0) (N (fl 0x211505) e0))) (N (N (N (fl 0x110402) e0) (N (fl 0x90705) e0)) (N (N (fl 0x110403) e0) (N (fl 0x211909) e0))))))) (N (N (N (N (N (N (N (fl 0x90302) (fl 0x252109)) (N (fl 0xb0503) e0)) (N (N (fl 0xa0502) e0) (N (fl 0xa0905) e0))) (N (N (N (fl 0x210905) e0) (N (fl 0x121103) e0)) (N (N (fl 0x210a02) e0) (N (fl 0x292105) e0)))) (N (N (N (N (fl 0x211102) (fl 0x252111)) (N (fl 0x210703) e0)) (N (N (fl 0x210602) e0) (N (fl 0x121105) e0))) (N (N (N (fl 0x130302) e0) (N (fl 0x292103) e0)) (N (N (fl 0x252102) e0) (N (fl 0x121109) e0))))) (N (N (N (N (N (fl 0x110502) (fl 0x211511)) (N (fl 0x230503) e0)) (N (N (fl 0x220502) e0) (N (fl 0x250905) e0))) (N (N (N (fl 0x70302) e0) (N (fl 0x311103) e0)) (N (N (fl 0x221102) e0) (N (fl 0x110b09) e0)))) (N (N (N (N (fl 0x110903) e0) (N (fl 0x190903) e0)) (N (N (fl 0x190902) e0) (N (fl 0x311105) e0))) (N (N (N (fl 0x90402) e0) (N (fl 0x210605) e0)) (N (N (fl 0x90403) e0) (N (fl 0x311109) e0)))))) (N (N (N (N (N (N (fl 0x210302) (fl 0x211211)) (N (fl 0x130503) e0)) (N (N (fl 0x120502) e0) (N (fl 0x150905) e0))) (N (N (N (fl 0x211109) e0) (N (fl 0x191103) e0)) (N (N (fl 0x151102) e0) (N (fl 0x110a09) e0)))) (N (N (N (N (fl 0x110503) e0) (N (fl 0xd0903) e0)) (N (N (fl 0xd0902) e0) (N (fl 0x191105) e0))) (N (N (N (fl 0x230302) e0) (N (fl 0x90605) e0)) (N (N (fl 0x312102) e0) (N (fl 0x151109) e0))))) (N (N (N (N (N (fl 0x110902) (fl 0x222111)) (N (fl 0x90703) e0)) (N (N (fl 0x90602) e0) (N (fl 0x110d05) e0))) (N (N (N (fl 0xb0302) e0) (N (fl 0x222103) e0)) (N (N (fl 0x211202) e0) (N (fl 0x110d09) e0)))) (N (N (N (N (fl 0x211103) e0) (N (fl 0x110b03) e0)) (N (N (fl 0x290902) e0) (N (fl 0x222105) e0))) (N (N (N (fl 0x210402) e0) (N (fl 0x110705) e0)) (N (N (fl 0x210403) e0) (N (fl 0x222109) e0)))))))) (C 10 (C 4 (C 1 (C 8 (C 2 (C 3 (C 18 (C 5 (C 9 (C 6 (C 33 (C 32 (M 3 0x2446100244510043051002444500438450061ea20061e9200c1e420061e32) (C 16 (M 3 0x45091004588900244610025045002484500c1e820041e620061e520021e460061e32) (W 0x41e820041e420021e320020223002021b0020217002020f))) (W 0x25091002608d0025885002448500242510041e860021e620021e460021e32004021f)) (W 0x250190024219002301900222190045e1a0043e1a0021e1a00202230020217)) (W 0x2602500248250024425002282500222190045e260043e260021e26002021f002021b)) (M 5 0x8484500860250024425002401d0062a190022219002601500a5015008441500a3015004281500220150020c150145e160143e1600a1e16002022700a021f0060217)) (M 12 0xe605100e68490076049018504900a48490114249007304900a28490076445007344500a2c45003603101124310112425007301900a301500e241500e1e920181e8a0071e860301e4a0035e320071e260111e1a0300213)) (C 16 (W 0x244450024231002282500226190026015002500d002480d002300d002240d0045e0e0043e0e0021e0e) (W 0x246410022231002262500230190026015002500d002480d002420d002280d002200d0045e0e0043e0e0021e0e00202230020213))) (C 16 (C 32 (C 3 (C 6 (W 0x234510024249002504500244310024825002601500230090045e0a0043e0a0021e0a) (W 0x22231002242500260190025019002421900230190022c1500228090045e0a0043e0a0021e0a)) (M 5 0x242510044849002483500822310044425006242500450190043019002221900644150023015002181500a600d006500d004480d004300d008280d0145e0a0143e0a00a1e0a)) (W 0x222310024425002281d0020a090045e0a0043e0a0021e0a002016b00201670020163002015f002015b002012700200ff)) (W 0x24c310022425002501500248090045e0a0043e0a0021e0a00201570020153004003f002014f002014b0020147002012300200fb))) (C 16 (C 32 (C 34 (C 3 (M 3 0x2505100242510045049002384900252450042231006482500242210022821002421900430190046015002301500c100900c5e2200c3e220061e22) (W 0x22621002222100230190023215002600d002500d002480d002280d002240d0045e0e0043e0e0021e0e00400f7)) (W 0x258850024451002504500244310024425002482100230190024415002600d0045e220043e220021e22002013b0020133)) (W 0x2505100222210022415002320d0045e220043e220021e22002020b0020207002020300201ff00201fb00201e300201d3002003b002011f)) (W 0x142610024821001422100258190024415001520d0045e220043e220021e2200201f700201f3004004f00201ef00201eb00201e700201df00201cf0040037))) (C 2 (C 8 (C 32 (C 16 (C 3 (C 9 (M 2 0x34251001504900248490012a4900250450014845001444500344310014231002601900150190014a190043015001480500128050085e060083e060041e06) (W 0x1586100142450015031002602500248250024425001282500224250012a1900122190016215001301500128050045e060043e060021e06)) (W 0x24c490022231002422500244190025015002600d002520d002480d002300d002280d0045e060043e060021e06)) (W 0x2223100250190045e060043e060021e0600200db00200d700200d300200cf00200cb00200c300200a3002007b)) (W 0x2243100242190045e060043e060021e0600200ef00200eb00200e700200e300200df00200d300200cf00200c700200a7002007f)) (W 0x228250022425002601900210050045e060043e060021e0600200bf00200bb004002300200b700200b3004001f00200af002009f0020077)) (W 0x26031002300d002280d00204050045e060043e060021e06002006f002006b004000f00200670020063004000b002005b004000700200570020053))) (C 1 (C 8 (C 2 (C 32 (C 16 (C 3 (C 5 (W 0x242510024c49002504500260310024825002301900244110045e120043e120021e12) (W 0x24265002283100222250023019002601500250150024415002381500224150045e120043e120021e12)) (W 0x244450022431002462500250190026015002480d002420d002300d002280d0045e0e0043e0e0021e0e)) (W 0x22825002500d0045e120043e120021e1200201b700201b300201af00201ab00201a7002019f002017f0020173)) (W 0x22425002480d0045e120043e120021e1200201cb00201c700201c300201bf00201bb00201af00201a700201a300201830020177)) (W 0x260250023019002221900208090045e0a0043e0a0021e0a002011b002011700400330020113002010f004002f002010b002010300200f3)) (W 0x14445002243100242210025211001600d0045e120043e120021e12002019b002019700400470020193002018f00400430020187002017b002016f004002b)) (W 0x2504900230150045e060043e060021e06002009b0020097004001b0020093002008f0040017002008b00200870040013002008300200730040003))) (C 32 (C 16 (C 1 (C 4 (C 33 (C 6 (M 3 0x42431006602900648290022829006222900428250064415006500d00c5e2a00c3e2a0061e2a00601370020133002012f002012b) (C 3 (W 0x2486100224290022825002601900250190023419002221900244150045e1a0043e1a0021e1a004011f) (W 0x14c290022c2900122290014425001282500144190022419001221900150150013015002600d001500d002480d001300d001280d0045e0e0043e0e0021e0e00400f7))) (W 0x14261001424d00242310026029002482900242290022829001222900242190022415001300d001220d0045e2a0043e2a0021e2a002013b002012b)) (C 3 (M 3 0x25051002484900660290024c290044829006422900438290022c290042825002242500622190044415002301500244110043011002241100c5e1200c3e120061e1200c018b00c0107) (W 0x222310024c2900242290022c29002501500244110022411002600d002480d002300d002280d0045e0e0043e0e0021e0e0020187002017b00400f3))) (C 33 (W 0x2523100260290024829002462900228290022229002261900230150025005002440500224050045e060043e060021e0600400ab00200870020073004005f) (M 3 0x44245002443100232310022431004622900260290044829006422900432290022229002482500428250024219004261900250150044415004600d002280d0063005004240500c5e0600c3e060061e0600c00ab00c009700c005f))) (C 4 (C 1 (W 0x25441002444100264310025029002482900242290022829002242500222190023015002600d0045e2a0043e2a0021e2a00401d7004013f) (W 0x248290022229002221900220050045e060043e060021e0600200db00200d700200d300200cf00200cb00200c300400ab00200a3002007b004005f)) (W 0x24c2900228250024411002500d0045e120043e120021e1200201b700201b300201af00201ab00201a7002019f004018b002017f002017300401070040017))) (C 4 (C 1 (C 16 (W 0x25861002544900240310024829002402900228290022229002442500242190025015002600d0045e2a0043e2a0021e2a00401db0040143) (W 0x260290022a25002201d00220150020c0d0045e2a0043e2a0021e2a002022b00202270020223002021f002021b00202170020213002020f00401d7004013f)) (W 0x24229002282900224190022c050045e060043e060021e0600200ef00200eb00200e700200e300200df002002700200d300200c700400ab00200a7002007f004005f)) (W 0x1242900122290014825001242500134110012211001480d0012a0d0045e120043e120021e1200201cb00201c700201c300201bf00201bb002004b00201af00201a3004018b002018300201770040107004001b))))
def cp_27_4 : CertItem := CI (some (BV 0x1000000e00000e00000c00000e00000c00000c00000a00000e00000c00000c00000a00000c00000a00000a00000800000e00000c00000c00000a00000c00000a00000a00000800000c00000a00000a00000800000a00000800000800000600000e00000c00000c00000a00000c00000a00000a00000800000c00000a00000a00000800000a00000800000800000600000c00000a00000a00000800000a00000800000800000600000a000008000008000006000008000006000006000004 0x9000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009000009 640 576)) 0 0x8000000000000000 e0 (C 3 (C 8 (C 0 (C 1 (M 2 0x2421100224110021211002220900218090010a090021e920021e8a0061e820021e620021e520061e420021e2a0021e1a0011e160011e0a) (W 0x1300500128050012405001180500114050010c0500304050055e060053e060031e06)) (M 2 0x24045001484100220290014025001202500140190022015001601100250110014411001421100130110016009001420900228090021809001480500144050013005002240500a5e0200a3e020061e02)) (M 4 0x24261008404100440250046021004442100428210022421004222100410190042015004601100450110024211002241100360090044809002300900160050041805004140500304050143e2200c1e220145e02)) (M 60 0x3c444100440290112425067202103c4019011221502b101503c421103840110041411074480d03c400d0a3300d03c280d011200d022100d03c080d038500902b2209038180901a120903c6005004500500418050331e2a0111e2612c3e0e06f1e0612c5e02))
def cp_27_5 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x21e0a0021e060043e02)
def cp_27_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x11e220011e120011e0a0011e060023e020011e02)
def wVec_28 : Fin 5 → ℕ := ![3,3,3,2,2]
def fastW_28 (m : ℕ) : ℕ := cond (bitAt m 0) 3 0 + cond (bitAt m 1) 3 0 + cond (bitAt m 2) 3 0 + cond (bitAt m 3) 2 0 + cond (bitAt m 4) 2 0
def cFn_28 (k i : ℕ) : ℕ × ℕ := (fastW_28 i + 1 * k, 10)
def rowZ_28 : ℕ → List ℕ
  | 0 => (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 22 0x1716140f0e0c19151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 6 0x110905030201)
  | 3 => [0]
  | _ => []
def rowO_28 : ℕ → List ℕ
  | 0 => (unpackBytes 3 0x201810)
  | _ => []
def rowFl_28 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x1d1b1a)
  | 1 => (unpackForbs 16 0x1915130000000000191512000000000019131200000000001513120000000000190d0b0000000000190d0a0000000000190b0a00000000000d0b0a0000000000150d070000000000130b070000000000150d060000000000120a060000000000130b040000000000120a04000000000013070400000000000b0704)
  | 2 => (unpackForbs 7 0x19150d000000000019130b000000000019120a00000000000d0b07000000000015120600000000000d0a060000000000131204)
  | 3 => (unpackForbs 30 0x1d191300000000001a191300000000001d151300000000001d191200000000001b191200000000001d151200000000001a151200000000001a131200000000001b190d00000000001a190d0000000000150f0d00000000001d190b00000000001a190b00000000001d0d0b00000000001b0d0b00000000001d190a00000000001b190a00000000001d0d0a00000000001a0d0a00000000000d0c0a00000000001b0b0a00000000001b130700000000001d0d0700000000001b0b0700000000001a120600000000001d0d0600000000000f0d0600000000001a0a0600000000001a120400000000001b0b04)
  | 4 => (unpackForbs 3 0x1d1b1900000000001d1a1900000000001b1a19)
  | 5 => (unpackForbs 9 0x11090500000000001109030000000000110503000000000009050300000000001109020000000000110502000000000009050200000000001103020000000000090302)
  | 6 => (unpackForbs 47 0x151109000000000013110900000000001211090000000000110d090000000000110b090000000000191105000000000013110500000000001211050000000000110d050000000000190905000000000015090500000000000b090500000000000a090500000000001107050000000000090705000000000011060500000000000906050000000000191103000000000015110300000000001211030000000000190903000000000013090300000000000d090300000000000a09030000000000090703000000000013050300000000000b050300000000000904030000000000191102000000000015110200000000001311020000000000110a020000000000190902000000000012090200000000000d090200000000000b0902000000000011060200000000000906020000000000150502000000000012050200000000000a0502000000000011040200000000000904020000000000130302000000000012030200000000000b030200000000000a0302)
  | 7 => (unpackForbs 16 0x15131100000000001912110000000000190d090000000000190b0900000000000d0b090000000000190a0900000000000d0a0900000000000b0a0900000000000d070500000000000d06050000000000130b0300000000000b0703000000000013040300000000000a060200000000001204020000000000060402)
  | 8 => (unpackForbs 6 0x11090100000000001105010000000000090501000000000011030100000000000903010000000000090201)
  | _ => []
def rowFbs_28 : ℕ → List (List ℕ)
  | 1 => (rowFl_28 0)
  | 2 => (rowFl_28 1) ++ (rowFl_28 2) ++ (rowFl_28 3) ++ (rowFl_28 4)
  | 3 => (rowFl_28 5) ++ (rowFl_28 6) ++ (rowFl_28 7)
  | 4 => (rowFl_28 8)
  | _ => []
def cp_28_0 : CertItem := CI none 0x177f7ffe 0x80808000 e0 (W 0)
def cp_28_1 : CertItem := CI none 0x17f7f7f 0x80000000 (fl 0x1d1b1a) (W 0x20003)
def cp_28_2 : CertItem := CI (some (BV 0xf00000c00000c00000900000c00000900000900000600000d00000a00000a00000700000a00000700000700000400000d00000a00000a00000700000a00000700000700000400000b000008000008000005000008000005000005000002 0xa00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a 272 320)) 0x10117 0x80000000 (N (N (N (N (N (N (fl 0xb0704) (fl 0x1b0b0a)) (N (fl 0x131204) (fl 0x1b1912))) (N (N (fl 0xd0b0a) (fl 0x1a190b)) (N (fl 0x1a1204) e0))) (N (N (N (fl 0x120a06) (fl 0x1b190a)) (N (fl 0x19120a) (fl 0x1d1913))) (N (N (fl 0x151312) (fl 0x1b190d)) (N (fl 0x1a1206) e0)))) (N (N (N (N (fl 0x120a04) (fl 0x1a0d0a)) (N (fl 0x151206) (fl 0x1d1513))) (N (N (fl 0x190d0a) (fl 0x150f0d)) (N (fl 0xf0d06) e0))) (N (N (N (fl 0x130b07) (fl 0x1b0d0b)) (N (fl 0x19150d) (fl 0x1d1a19))) (N (N (fl 0x191512) (fl 0x1a1512)) (N (fl 0x1d0d07) e0))))) (N (N (N (N (N (fl 0x130704) (fl 0xd0c0a)) (N (fl 0xd0a06) (fl 0x1d1912))) (N (N (fl 0x190b0a) (fl 0x1d190b)) (N (fl 0x1a0a06) e0))) (N (N (N (fl 0x150d06) (fl 0x1d190a)) (N (fl 0x19130b) (fl 0x1b1a19))) (N (N (fl 0x191312) (fl 0x1a1312)) (N (fl 0x1b0b07) e0)))) (N (N (N (N (fl 0x130b04) (fl 0x1d0d0a)) (N (fl 0xd0b07) (fl 0x1a1913))) (N (N (fl 0x190d0b) (fl 0x1a190d)) (N (fl 0x1d0d06) e0))) (N (N (N (fl 0x150d07) (fl 0x1d0d0b)) (N (fl 0x1b0b04) (fl 0x1d1b19))) (N (N (fl 0x191513) (fl 0x1d1512)) (N (fl 0x1b1307) e0)))))) (C 24 (C 12 (C 3 (C 5 (C 17 (M 2 0x2345100232510023829002282500324250032e4a0041e2a0011e260032e1a0011e1a) (M 4 0x4384500822290042825004341900c2e460021e2a0081e260021e1a00100bb00300b70070033002001b)) (M 4 0x12829001242900122290072425004381500432150040c1500c2e1600c1e160050083004001b00b004b)) (M 2 0x4282900228250023815002340d002320d0020a0d0062e0e0061e0e0020043001000f004000b00300070010003)) (C 10 (C 17 (C 9 (M 3 0x33231003340d0030a0d0012e520082e4a0091e3200100cb006001f002006f0010017) (W 0x128310022825002120d0022e4a0031e260012e1a002008f001008b0020087001007f0020047)) (M 2 0x23445004243100422310062e460061e3200100bf0020033001007b003001f00400130020063002000b)) (W 0x13229001222900518290012e4a0022e460031e2a00300ab001009f001009b0030023002004f002006b002000f))) (C 12 (C 10 (C 9 (C 17 (C 18 (M 2 0x23015004300d0062e520041e1a0021e1600100df00100db00100d7) (W 0x2300d0032e4a0011e1a0021e1600100d300100cf003003f001007f)) (W 0x2300d0032e460021e1a0011e1600100c700100c3003003b00300370010073)) (W 0x3304900230190013015002300d0032e520031e260010097004009300300530010067)) (W 0x1305100130450023029002282900222290031e2a0012e1a0022e1600200a700200a3003005700300270010077002005f)) (M 2 0x2303100424310043015004300d0012e4a0052e460061e32001003700200b300200af006005b006002f006002b004007b)))
def cp_28_3 : CertItem := CI (some (BV 0x1000000d00000d00000a00000d00000a00000a00000700000e00000b00000b00000800000b00000800000800000500000e00000b00000b00000800000b00000800000800000500000c000009000009000006000009000006000006000003 0xa00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a 304 320)) 1 0x80000000 (N (N (N (N (N (N (N (fl 0x90302) (fl 0xb0a09)) (N (fl 0xa0903) e0)) (N (N (fl 0x120502) e0) (N (fl 0x121105) e0))) (N (N (N (fl 0x110905) e0) (N (fl 0x110605) e0)) (N (N (fl 0x110a02) e0) (N (fl 0x60402) e0)))) (N (N (N (N (fl 0x110902) (fl 0x190b09)) (N (fl 0x121103) e0)) (N (N (fl 0xb0902) e0) (N (fl 0x110d09) e0))) (N (N (N (fl 0x130302) e0) (N (fl 0xb0905) e0)) (N (N (fl 0x90403) e0) (N (fl 0xb0703) e0))))) (N (N (N (N (N (fl 0x90502) (fl 0x190a09)) (N (fl 0x130903) e0)) (N (N (fl 0x90602) e0) (N (fl 0x191105) e0))) (N (N (N (fl 0xb0302) e0) (N (fl 0x110705) e0)) (N (N (fl 0x151102) e0) (N (fl 0xa0602) e0)))) (N (N (N (N (fl 0x110503) (fl 0x191211)) (N (fl 0x191103) e0)) (N (N (fl 0x120902) e0) (N (fl 0x131109) e0))) (N (N (N (fl 0x110402) e0) (N (fl 0x190905) e0)) (N (N (fl 0x130503) e0) (N (fl 0xd0605) e0)))))) (N (N (N (N (N (N (fl 0x110302) (fl 0xd0a09)) (N (fl 0xd0903) e0)) (N (N (fl 0x150502) e0) (N (fl 0x131105) e0))) (N (N (N (fl 0xa0302) e0) (N (fl 0x90705) e0)) (N (N (fl 0x131102) e0) (N (fl 0x120402) e0)))) (N (N (N (N (fl 0x90503) (fl 0x190d09)) (N (fl 0x151103) e0)) (N (N (fl 0xd0902) e0) (N (fl 0x121109) e0))) (N (N (N (fl 0x90402) e0) (N (fl 0x150905) e0)) (N (N (fl 0xb0503) e0) (N (fl 0x130b03) e0))))) (N (N (N (N (N (fl 0x110502) (fl 0xd0b09)) (N (fl 0x190903) e0)) (N (N (fl 0x110602) e0) (N (fl 0x110b09) e0))) (N (N (N (fl 0x120302) e0) (N (fl 0xa0905) e0)) (N (N (fl 0x191102) e0) (N (fl 0x130403) e0)))) (N (N (N (N (fl 0x110903) (fl 0x151311)) (N (fl 0x90605) e0)) (N (N (fl 0x190902) e0) (N (fl 0x151109) e0))) (N (N (N (fl 0xa0502) e0) (N (fl 0x110d05) e0)) (N (N (fl 0x90703) e0) (N (fl 0xd0705) e0))))))) (C 4 (C 1 (C 2 (C 9 (C 8 (M 6 0x6284900528450042445001243100530190063015004300d002200d0182e4200b1e3200c1e2a0011e1a001011f003011b) (C 16 (M 2 0x210190021015002100d0042e4a0042e460081e2200301170030113001010f) (M 2 0x10c150010c0d0010a0d0082e420081e2200400df00400db00400d700400d300400cf))) (M 2 0x118290042825004242500220190021215002120d0022e460062e420081e26002011b004010b00301070030103)) (C 8 (W 0x128090012209001180900112090010a090042e0a0041e0a003009b0010097001009300100f700100f300100ef) (W 0x122090010a090042e0a0041e0a003008f002008b005001f00200870020083001007f0010073))) (C 8 (C 16 (M 2 0x2182900228050022405002180500214050020c050082e060081e0600100eb00100e700100e30020033003002f0030027) (W 0x114050010c050042e060041e06003006f002006b00200670020063001004f001003b0030007001002b)) (W 0x124050010c050042e060041e06003005f002005b005001300200570020053001004b00100370040003))) (C 16 (C 8 (M 2 0x1303900534110022411002221100314110021211002080d00530090082e120081e1200200ff00200fb002007b001007700400470020043002003f) (W 0x12211001080d0042e120041e1200300bb00200b700200b300200af00100a7001009f0040017004000b)) (W 0x11211001080d0042e120041e1200300cb00200c700200c300200bf002002300200b300100af00100ab00100a3004001b004000f)))
def cp_28_4 : CertItem := CI (some (BV 0x1100000e00000e00000b00000e00000b00000b00000800000f00000c00000c00000900000c00000900000900000600000f00000c00000c00000900000c00000900000900000600000d00000a00000a00000700000a000007000007000004 0xa00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a00000a 336 320)) 0 0x80000000 (N (N (N (fl 0x90201) (fl 0x110501)) (N (fl 0x110301) e0)) (N (N (fl 0x90301) (fl 0x110901)) (N (fl 0x90501) e0))) (C 0 (M 2 0x12411002121100230090022209002180900230050012805001240500214050012e520082e420081e220012e120021e12) (C 8 (W 0x13045001180900112090012805001240500114050052e020051e020030013001000b) (W 0x122210052e020051e020040017003000f00300070030003)))
def cp_28_5 : CertItem := CI none 0 0x80000000 e0 (W 0x21e120021e0a0021e060052e02)
def cp_28_6 : CertItem := CI none 0 0x80000000 e0 (W 0x41e02)
def cp_28_7 : CertItem := CI none 0 0x80000000 e0 (W 0)
def wVec_29 : Fin 6 → ℕ := ![3,3,3,3,3,3]
def fastW_29 (m : ℕ) : ℕ := cond (bitAt m 0) 3 0 + cond (bitAt m 1) 3 0 + cond (bitAt m 2) 3 0 + cond (bitAt m 3) 3 0 + cond (bitAt m 4) 3 0 + cond (bitAt m 5) 3 0
def cFn_29 (k i : ℕ) : ℕ × ℕ := (fastW_29 i + 1 * k, 12)
def rowZ_29 : ℕ → List ℕ
  | 0 => (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowO_29 : ℕ → List ℕ
  | 0 => (unpackBytes 3 0x403020)
  | _ => []
def rowFl_29 : ℕ → List (List ℕ)
  | 0 => ((unpackForbs 64 0x272600000000000032240000000000002b240000000000002a24000000000000272400000000000026240000000000002d1d000000000000391b000000000000331b0000000000002b1b0000000000001d1b000000000000391a000000000000321a0000000000002a1a0000000000001d1a0000000000001b1a0000000000003517000000000000331700000000000027170000000000001d170000000000001b170000000000003516000000000000321600000000000026160000000000001d160000000000001a1600000000000017160000000000003314000000000000321400000000000024140000000000001b140000000000001a14000000000000171400000000000016140000000000002d0f0000000000002b0f000000000000270f0000000000001d0f0000000000001b0f000000000000170f0000000000002d0e0000000000002a0e000000000000260e0000000000001d0e0000000000001a0e000000000000160e0000000000000f0e0000000000002b0c0000000000002a0c000000000000240c0000000000001b0c0000000000001a0c000000000000140c0000000000000f0c0000000000000e0c0000000000002708000000000000260800000000000024080000000000001708000000000000160800000000000014080000000000000f080000000000000e080000000000000c08) ++ (unpackForbs 10 0x3533000000000000353200000000000033320000000000002d2b000000000000392a0000000000002d2a0000000000002b2a0000000000002d270000000000002b270000000000002d26))
  | 1 => (unpackForbs 40 0x3933310000000000353331000000000039323100000000002d2b290000000000392a2900000000002d2a2900000000002d2725000000000035262500000000002b27230000000000332423000000000032262200000000002a2622000000000032242200000000002a242200000000002624220000000000391d1900000000001d1b190000000000391a1900000000001d1a1900000000001b1a1900000000001d1715000000000035161500000000001b1713000000000033141300000000001a1612000000000032141200000000001d0f0d00000000002d0e0d00000000002b1b0b00000000001b0f0b00000000002b0c0b00000000002a0e0a00000000002a0c0a00000000002717070000000000170f0700000000002708070000000000160e0600000000002608060000000000140c040000000000240804)
  | 2 => (unpackForbs 60 0x312900000000000031250000000000002925000000000000312300000000000029230000000000002523000000000000312200000000000029220000000000002522000000000000232200000000000031190000000000002919000000000000311500000000000025150000000000001915000000000000311300000000000023130000000000001913000000000000151300000000000031120000000000002212000000000000191200000000000015120000000000001312000000000000290d000000000000250d000000000000190d000000000000150d000000000000290b000000000000230b000000000000190b000000000000130b0000000000000d0b000000000000290a000000000000220a000000000000190a000000000000120a0000000000000d0a0000000000000b0a00000000000025070000000000002307000000000000150700000000000013070000000000000d070000000000000b0700000000000025060000000000002206000000000000150600000000000012060000000000000d060000000000000a06000000000000070600000000000023040000000000002204000000000000130400000000000012040000000000000b040000000000000a0400000000000007040000000000000604)
  | 3 => (unpackForbs 56 0x312921000000000031252100000000002925210000000000312321000000000029232100000000002523210000000000312221000000000029222100000000002522210000000000232221000000000031191100000000003115110000000000191511000000000019131100000000001513110000000000151211000000000013121100000000002919090000000000290d090000000000190d090000000000290b090000000000190b0900000000000d0b090000000000290a090000000000190a0900000000000d0a0900000000000b0a0900000000002515050000000000150d050000000000250705000000000015070500000000000d07050000000000250605000000000015060500000000000d0605000000000007060500000000002313030000000000230b030000000000130b030000000000230703000000000013070300000000000b07030000000000230403000000000013040300000000000b0403000000000007040300000000002212020000000000220a020000000000120a020000000000220602000000000012060200000000000a06020000000000220402000000000012040200000000000a04020000000000060402)
  | 4 => (unpackForbs 15 0x211100000000000021090000000000001109000000000000210500000000000011050000000000000905000000000000210300000000000011030000000000000903000000000000050300000000000021020000000000001102000000000000090200000000000005020000000000000302)
  | 5 => (unpackForbs 15 0x21110100000000002109010000000000110901000000000021050100000000001105010000000000090501000000000021030100000000001103010000000000090301000000000005030100000000002102010000000000110201000000000009020100000000000502010000000000030201)
  | _ => []
def rowFbs_29 : ℕ → List (List ℕ)
  | 1 => (rowFl_29 0)
  | 2 => (rowFl_29 1) ++ (rowFl_29 2)
  | 3 => (rowFl_29 3) ++ (rowFl_29 4)
  | 4 => (rowFl_29 5)
  | _ => []
def cp_29_0 : CertItem := CI none 0x117177f177f7ffe 0x8000800080000000 e0 (W 0)
def cp_29_1 : CertItem := CI (some (BV 0x1300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001000000d00000d00000a00000d00000a00000a00000700000d00000a00000a00000700000a00000700000700000400001000000d00000d00000a00000d00000a00000a00000700000d00000a00000a00000700000a00000700000700000400000d00000a00000a00000700000a00000700000700000400000a000007000007000004000007000004000004000001 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 640 768)) 0x101170117177f 0x8000000000000000 (N (N (N (N (N (N (N (fl 0xc08) (fl 0x2d26)) (N (fl 0x1a14) e0)) (N (N (fl 0x2b0c) e0) (N (fl 0x1b1a) e0))) (N (N (N (fl 0x2708) (fl 0x3532)) (N (fl 0x2616) e0)) (N (N (fl 0x170f) e0) (N (fl 0x391b) e0)))) (N (N (N (N (fl 0x1608) (fl 0x2d2a)) (N (fl 0x3314) e0)) (N (N (fl 0x1d0e) e0) (N (fl 0x391a) e0))) (N (N (N (fl 0x1a0c) e0) (N (fl 0x1d17) e0)) (N (N (fl 0x2b0f) e0) (N (fl 0x2a24) e0))))) (N (N (N (N (N (fl 0xf08) (fl 0x2d27)) (N (fl 0x2414) e0)) (N (N (fl 0x160e) e0) (N (fl 0x2a1a) e0))) (N (N (N (fl 0xf0c) e0) (N (fl 0x3516) e0)) (N (N (fl 0x1d0f) e0) (N (fl 0x2624) e0)))) (N (N (N (N (fl 0x2408) (fl 0x2d2b)) (N (fl 0x1a16) e0)) (N (N (fl 0x2a0e) e0) (N (fl 0x2b1b) e0))) (N (N (N (fl 0x240c) e0) (N (fl 0x3317) e0)) (N (N (fl 0x1614) e0) (N (fl 0x3224) e0)))))) (N (N (N (N (N (N (fl 0xe08) (fl 0x2b27)) (N (fl 0x1b14) e0)) (N (N (fl 0xf0e) e0) (N (fl 0x1d1a) e0))) (N (N (N (fl 0xe0c) (fl 0x3533)) (N (fl 0x3216) e0)) (N (N (fl 0x1b0f) e0) (N (fl 0x2d1d) e0)))) (N (N (N (N (fl 0x1708) (fl 0x392a)) (N (fl 0x1716) e0)) (N (N (fl 0x260e) e0) (N (fl 0x1d1b) e0))) (N (N (N (fl 0x1b0c) e0) (N (fl 0x2717) e0)) (N (N (fl 0x2d0f) e0) (N (fl 0x2b24) e0))))) (N (N (N (N (N (fl 0x1408) (fl 0x2b2a)) (N (fl 0x3214) e0)) (N (N (fl 0x1a0e) e0) (N (fl 0x321a) e0))) (N (N (N (fl 0x140c) e0) (N (fl 0x1b17) e0)) (N (N (fl 0x270f) e0) (N (fl 0x2724) e0)))) (N (N (N (N (fl 0x2608) (fl 0x3332)) (N (fl 0x1d16) e0)) (N (N (fl 0x2d0e) e0) (N (fl 0x331b) e0))) (N (N (N (fl 0x2a0c) e0) (N (fl 0x3517) e0)) (N (N (fl 0x1714) e0) (N (fl 0x2726) e0))))))) (C 7 (C 11 (C 13 (C 14 (C 19 (C 21 (C 22 (C 25 (C 26 (C 35 (W 0x25e9a0025e960023e7200101270010123001011f002011b0020117) (W 0x45e8e0023e7200200fb00200f700200f300200ef00200eb)) (W 0x25e960025e8e0043e6a002010b00200e300200df00200db00200d7)) (W 0x25e960025e8e0043e66002010700200d300200cf00200cb00200c700200c3)) (W 0x25eaa0015e960015e8e0043e5a00100eb00200cb00200bf00200bb00200b700200b300200af)) (W 0x25e9a0025e8e0043e56002010f00200df00200ab00200a700200a3002009f002009b0020097)) (W 0x25e9a0025e960043e4e002010f00200e70020093002008f002008b00200870020083002007f002007b)) (W 0x45e3a0043e3a00100eb00200cb00100a700100a3001008f001008b00200770020073002006f002006b00200670020063)) (W 0x45e360043e36002011f001010700100f700100ef00100af0010087002005f002005b00200570020053002004f002004b0020047)) (W 0x45e2e0043e2e002011f001010b001010300100ff00100b3001009f0020043002003f002003b00200370020033002002f002002b0020027)) (W 0x45e1e0043e1e002011f001011b0010113001010f00100d700100c70020023002001f002001b00200170020013002000f002000b00200070020003))
def cp_29_2 : CertItem := CI (some (BV 0x1400001100001100000e00001100000e00000e00000b00001100000e00000e00000b00000e00000b00000b00000800001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b00000800000800000500001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b00000800000800000500000e00000b00000b00000800000b00000800000800000500000b000008000008000005000008000005000005000002 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 704 768)) 0x100010117 0x8000000000000000 (N (N (N (N (N (N (N (fl 0x240804) (fl 0x190a)) (N (fl 0x352625) (fl 0x3123))) (N (N (fl 0x331413) (fl 0x3112)) (N (fl 0x706) e0))) (N (N (N (fl 0x2a0e0a) (fl 0x150d)) (N (fl 0x604) e0)) (N (N (fl 0x391d19) (fl 0x2919)) (N (fl 0xd07) e0)))) (N (N (N (N (fl 0x270807) (fl 0x130b)) (N (fl 0x2d2b29) e0)) (N (N (fl 0x1b1a19) (fl 0x3113)) (N (fl 0x1506) e0))) (N (N (N (fl 0x2d0e0d) (fl 0x1312)) (N (fl 0x1204) e0)) (N (N (fl 0x2a2622) (fl 0x2922)) (N (fl 0x2507) e0))))) (N (N (N (N (N (fl 0x260806) (fl 0x290a)) (N (fl 0x2d2a29) (fl 0x3125))) (N (N (fl 0x351615) (fl 0x1913)) (N (fl 0xd06) e0))) (N (N (N (fl 0x1b0f0b) (fl 0x250d)) (N (fl 0xa04) e0)) (N (N (fl 0x2a2422) (fl 0x2322)) (N (fl 0x1507) e0)))) (N (N (N (N (fl 0x271707) (fl 0x230b)) (N (fl 0x353331) e0)) (N (N (fl 0x391a19) (fl 0x2515)) (N (fl 0x2506) e0))) (N (N (N (fl 0x321412) (fl 0x1912)) (N (fl 0x2204) e0)) (N (N (fl 0x332423) (fl 0x2523)) (N (fl 0xd0a) e0)))))) (N (N (N (N (N (N (fl 0x140c04) (fl 0x220a)) (N (fl 0x2d2725) (fl 0x2925))) (N (N (fl 0x1b1713) (fl 0x1513)) (N (fl 0xa06) e0))) (N (N (N (fl 0x2b0c0b) (fl 0x190d)) (N (fl 0x704) e0)) (N (N (fl 0x262422) (fl 0x3119)) (N (fl 0x1307) e0)))) (N (N (N (N (fl 0x170f07) (fl 0x190b)) (N (fl 0x393231) e0)) (N (N (fl 0x1d1a19) (fl 0x1915)) (N (fl 0x2206) e0))) (N (N (N (fl 0x1d0f0d) (fl 0x1512)) (N (fl 0x1304) e0)) (N (N (fl 0x322622) (fl 0x3122)) (N (fl 0xb0a) e0))))) (N (N (N (N (N (fl 0x160e06) (fl 0xd0b)) (N (fl 0x392a29) (fl 0x3129))) (N (N (fl 0x1d1715) (fl 0x2313)) (N (fl 0x1206) e0))) (N (N (N (fl 0x2b1b0b) (fl 0x290d)) (N (fl 0xb04) e0)) (N (N (fl 0x322422) (fl 0x2522)) (N (fl 0x2307) e0)))) (N (N (N (N (fl 0x2a0c0a) (fl 0x290b)) (N (fl 0x393331) e0)) (N (N (fl 0x1d1b19) (fl 0x3115)) (N (fl 0xb07) e0))) (N (N (N (fl 0x1a1612) (fl 0x2212)) (N (fl 0x2304) e0)) (N (N (fl 0x2b2723) (fl 0x2923)) (N (fl 0x120a) e0))))))) (C 12 (C 34 (C 5 (C 3 (C 9 (C 17 (C 6 (C 18 (C 10 (C 20 (C 24 (C 33 (C 36 (C 48 (M 2 0x22a4d0014c390026235002642d0045ea20015e9a0025e960025e8e0023e720023e6a0023e660023e5a0015e3a0023e1e0020093002008f) (M 2 0x22a4d0012c390024a35002602d0025eb20025eaa0025ea60025e9a0025e8e0023e720023e6a0023e660013e5a0013e3a0023e1e002009b0020097008018f)) (M 2 0x22c390012a35002462d002481d00a5e920023e720023e6a0023e660013e560023e4e0013e36008018b008018700200870020083)) (M 2 0x22c390012a35002422d002421d00a5e860023e720023e6a0023e660013e560023e4e0013e36008017700801730020073008016f002006f)) (M 2 0x2646100262610012c550012c4d0012a4d00230390023035002302d002681d0025eb20025eaa0025ea60025e9a0015e960015e8e00a3e62007016f001006700801670080163002005f002005b)) (M 2 0x26451001465100234510023251002284d0022835002622d002281d0025eb20025eaa0025e9a0025e9600a3e520025e3a0070173001006b008015f008015b0080157002004f002004b)) (M 2 0x2582900252290024c290024629002382900232290022c2900226290021a29002141d00a5e2a00a3e2a002009f001018b0020077006016f005015f001015b002004b008011f0080117002002b0020027)) (W 0x17049001684900162490015849001384900132490012a490011c35001242d001241d0015eaa0015ea60015e9a0015e960015e8e0053e4a00201870020173002016f0040153004014b0010047004014700100430040113)) (M 2 0x27019002681900264190026219002541900234190022a1900226190021a19002161900a5e1a00a3e1a001018f002008b0010177005017300200670060167002005700800f300800eb00800e7002001700800df0020013)) (M 3 0x37045003644500352450064845003464500338450032c4500322350031c2d006222900268190024a19003341900322190035eb20035eaa0015ea20035e9a00f3e460035e1e0025e1a0050187001008300c014300c013f00c013b003003f00c0137003003b00c0133006011f)) (M 2 0x27025002682500264250026225002582500254250024a250024625002382500234250022a2500226250021c25002121d00a5e2600a3e26008018b0050147008010b0080107008010300800ff002001f00800f7002001b00300eb00300e7)) (W 0x15835001700d001680d001640d001620d001540d001520d0014c0d0014a0d001340d001320d0012c0d0012a0d0011c0d0013e720055e0e0043e0e00401870020167002015f002015700400bb00400b700400b3001000700400af00400ab001000300400a7)) (M 2 0x2701500268150026415002581500252150024c150024615002381500232150022c1500226150021c15002161500a5e1600a3e16005018f00301670030163002014b002002f006011300800db00800d700800d300800cf002000f00800c7002000b00800c300800a3)) (C 5 (M 2 0x270890026889002628900258890024a890024469002446500244590024455002444d0024439002442d002441d0015ea60095e8a0023e720013e360073e260080183008017f002007f008017b002007b008016b0040157008014f004013b0040137008011b001002300800ef00800bf) (W 0x2441500230150012c1500126150011c1500116150055e160053e160040183004017f001007f001007b00100630010053004014f004011b00400db00400d700400d300400cf001000f00400c7001000b00400c300400a3))) (C 18 (W 0x17031001683100164310016231001543100152310014c310014a31001343100132310012c310012a31001182d001181d0055e320053e320040183002013f004012f004012b0040127004012300100370010033004010f00400fb00400e300400cb00200bb00200b3) (W 0x2423100132310012a310022431001182d001181d0055e320053e320010073001006f0040153004014f001004700100430040133004012f004012b0040127004012300100370010033004010f00400fb00400e300400cb00400b7)))
def cp_29_3 : CertItem := CI (some (BV 0x1500001200001200000f00001200000f00000f00000c00001200000f00000f00000c00000f00000c00000c00000900001200000f00000f00000c00000f00000c00000c00000900000f00000c00000c00000900000c00000900000900000600001200000f00000f00000c00000f00000c00000c00000900000f00000c00000c00000900000c00000900000900000600000f00000c00000c00000900000c00000900000900000600000c000009000009000006000009000006000006000003 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 768 768)) 1 0x8000000000000000 (N (N (N (N (N (N (N (fl 0x60402) (fl 0x2103)) (N (fl 0x290a09) e0)) (N (N (fl 0x230703) e0) (N (fl 0x292221) e0))) (N (N (N (fl 0x220a02) e0) (N (fl 0x151211) e0)) (N (N (fl 0xd0705) e0) (N (fl 770) e0)))) (N (N (N (N (fl 0xa0602) (fl 0x1109)) (N (fl 0x190d09) e0)) (N (N (fl 0x70605) e0) (N (fl 0x312321) e0))) (N (N (N (fl 0x130403) e0) (N (fl 0x311511) e0)) (N (N (fl 0x251505) e0) (N (fl 0x2102) e0))))) (N (N (N (N (N (fl 0x120402) (fl 0x1105)) (N (fl 0x190b09) e0)) (N (N (fl 0x230b03) e0) (N (fl 0x252321) e0))) (N (N (N (fl 0x70403) e0) (N (fl 0x191311) e0)) (N (N (fl 0x250705) e0) (N (fl 0x902) e0)))) (N (N (N (N (fl 0x220602) (fl 0x2111)) (N (fl 0x291909) e0)) (N (N (fl 0x150605) e0) (N (fl 0x312521) e0))) (N (N (N (fl 0xb0703) e0) (N (fl 0x232221) e0)) (N (N (fl 0xd0a09) e0) (N (fl 0x903) e0)))))) (N (N (N (N (N (N (fl 0xa0402) (fl 0x905)) (N (fl 0xd0b09) e0)) (N (N (fl 0x130b03) e0) (N (fl 0x312221) e0))) (N (N (N (fl 0x221202) e0) (N (fl 0x151311) e0)) (N (N (fl 0x150705) e0) (N (fl 0x502) e0)))) (N (N (N (N (fl 0x120602) (fl 0x2109)) (N (fl 0x290d09) e0)) (N (N (fl 0xd0605) e0) (N (fl 0x292521) e0))) (N (N (N (fl 0x230403) e0) (N (fl 0x311911) e0)) (N (N (fl 0xb0a09) e0) (N (fl 0x503) e0))))) (N (N (N (N (N (fl 0x220402) (fl 0x2105)) (N (fl 0x290b09) e0)) (N (N (fl 0x231303) e0) (N (fl 0x292321) e0))) (N (N (N (fl 0xb0403) e0) (N (fl 0x191511) e0)) (N (N (fl 0x150d05) e0) (N (fl 0x1102) e0)))) (N (N (N (N (fl 0x120a02) e0) (N (fl 0x131211) e0)) (N (N (fl 0x250605) e0) (N (fl 0x312921) e0))) (N (N (N (fl 0x130703) e0) (N (fl 0x252221) e0)) (N (N (fl 0x190a09) e0) (N (fl 0x1103) e0))))))) (C 8 (C 1 (C 4 (C 2 (C 32 (C 9 (C 3 (C 6 (C 18 (C 24 (C 16 (W 0x34231003482900360150035ea20035e8a0033e520033e46) (C 5 (C 10 (W 0x3444500342310035ea20035e920063e4200300b3) (W 0x34829003422900322290065e2a0063e2a00300b3)) (W 0x360150035015003441500314150065e160063e1600300a3))) (W 0x348610034231003222900330150035ea20035e8a0063e6200300b700300af)) (W 0x3504900348490034249003243100322290035e8a0063e4a0035e1600300ab00300a7)) (W 0x34c4100360310035019003441900342190033019003221900314150065e1a0063e1a00300a7)) (W 0x34641003422900360190035015003480d003440d003300d003280d003180d0065e0e0063e0e003009f)) (C 16 (W 0x32231003282900360250034425003242500312190035015003480d0065e260063e26) (M 2 0x3486500344650065241006323100632290034825003442500642250122025003201d00612190035015003500d0030a0d00c5e2600c3e2600600b700300a700300a3003009f))) (C 12 (C 17 (C 3 (C 5 (C 33 (C 34 (C 36 (W 0x3242500330190065e820033e520033e2a00300df006011b) (W 0x348290022425002301900112190065e820023e620033e5200300db00300d7006011b)) (W 0x3282900312190065e820033e620033e4a00300d300300cf00300cb006011b)) (W 0x3282900312190065e820033e620033e4a00300c700300c300300bf00300bb006011b)) (W 0x32425003281d0034415003301500314150030c150065e160063e1600300df00300bf006011b)) (W 0x34049003402900312190034015003640d003540d0034a0d003300d003280d0065e0e0063e0e00200d700200cf00300c7006011b)) (M 4 0x6405100c4049006684500c644500c5045006484500c222900c44250064619006221900c3015006400d006280d0185e820183e4600300db00900c700300bf018011b)) (W 0x340610034051003403500368310035431003243100322310034029003442500370190031815003180d0065e320063e3200300df00300bf006011b))) (C 3 (C 5 (C 6 (C 9 (C 10 (M 4 0x25061007426100550510054251002305100550450074845007603100548310027009005580900238090185e0a0183e0a018010300c004f01800ff) (W 0x348290034229003282900322290065e0a0063e0a006010300600ff003004b0030047)) (W 0x3484500342310036025003502500330250032825003520900332090065e0a0063e0a0060103002004f00600ff0020047)) (W 0x3501900342190033019003221900312190065e0a0063e0a006010300600ff0030043003003f003003b)) (W 0x322250036015003501500342150033015003281500318150034a0900332090032a090031a090065e0a0063e0a006010300600ff00300470030043)) (W 0x3600d003500d003480d003300d003280d003180d0065e0a0063e0a006010300600ff00300370030033003002f003002b))) (C 3 (C 5 (C 6 (C 9 (C 10 (W 0x342610035049003444500360310065e120063e12006010f0030073006010b00600f7) (W 0x360290034429003422900324290032229003541100334110065e120063e12006010f0020073006010b002006f00600f7)) (W 0x3444500342290036025003502500330250032425003521100332110065e120063e12006010f0020073006010b002006f00600f7)) (W 0x3501900342190033019003221900312190065e120063e12006010f006010b003006b0030067003006300600f7)) (W 0x3501500344150033015003241500314150065e120063e12006010f006010b003005f003005b0030057003005300600f7)) (M 2 0x3444500342250032225003601d003441d003421d006241d006141d00352110033211003600d006500d006300d015080d00c5e0e00c3e0e00c010f006007300c010b00300630030057003005300c00f7))) (C 3 (C 5 (C 6 (C 9 (C 10 (M 4 0x25061007446100550510054451002305100550490074849007603100548310027005005580500238050185e060183e0601800f300c002701800ef01800e701800e3) (W 0x34849003443100360290033029003282900334050065e060063e0600600f3003002700600ef00600e700600e3)) (W 0x3602500348250034425003282500324250065e060063e0600600f300600ef0030023003001f00600e700600e3)) (W 0x324290036019003501900344190033019003281900318190034c0500334050032c050031c050065e060063e0600600f3002002700600ef002001f00600e700600e3)) (W 0x36015003501500344150033015003241500314150065e060063e0600600f300600ef003001b0030017003001300600e700600e3)) (W 0x3600d003500d003480d003300d003280d003180d0065e060063e0600600f300600ef00600e7003000f003000b0030007003000300600e3))) (C 9 (C 10 (C 3 (C 5 (C 6 (M 2 0x358890037085003445100342510037049003484900622310066021003482100c5e2200c3e2200c0117006009b00c011300c010700c00fb00c00eb) (W 0x344210032421003601900354190034219003341900322190065e1a0063e1a0060117002009b00601130020093003006b003006700600fb00600eb)) (M 2 0x348450036021006422100328210032221003701500360150065215006441500338150033215006241500c5e1600c3e1600c0117003009b00c011300300970030093003005f003005b006005300c00fb00c00eb)) (W 0x342210032421003222100310190033215003600d003520d003480d003340d003280d0031c0d0065e0e0063e0e0060117002009b00601130020093006010700300fb003003700600eb)) (W 0x348290032829003222900342190032415003600d0065e220063e2200601170060113003008f003008b0030087006010700600fb00600eb)) (W 0x344250032825003242500322190036015003480d0065e220063e22006011700601130030083003007f003007b0030077006010700600fb00600eb)))
def cp_29_4 : CertItem := CI (some (BV 0x1600001300001300001000001300001000001000000d00001300001000001000000d00001000000d00000d00000a00001300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001000000d00000d00000a00000d00000a00000a00000700000d00000a00000a00000700000a000007000007000004 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 832 768)) 0 0x8000000000000000 (N (N (N (N (fl 0x30201) (fl 0x210301)) (N (fl 0x210201) (fl 0x110901))) (N (N (fl 0x90201) (fl 0x110501)) (N (fl 0x90301) (fl 0x211101)))) (N (N (N (fl 0x50201) (fl 0x90501)) (N (fl 0x50301) (fl 0x210901))) (N (N (fl 0x110201) (fl 0x210501)) (N (fl 0x110301) e0)))) (C 8 (C 1 (C 4 (C 2 (C 17 (C 16 (C 0 (M 2 0x148290024025002142500250190021819002501500148150014015002480d002400d0045e8a0045e860055e820043e620043e520043e4a0015e320013e320013e2a) (M 2 0x2406100242510024051002604900242490026031002403100348290024425002402500250190024019001501500230150011415001500d001480d002440d00e5e0200e3e02)) (M 2 0x2504900230490025041002484100244410024241002203100228290021829002282500220250026019002201900260150022015002300d002200d0025e920025e8a0025e860015e8200e3e420075e02009003b)) (M 2 0x23049002604500450450044845004444500230450022845002244500222290022825004221900260150021415004180d0045e860015e8200e3e460025e260075e02009003b)) (M 2 0x14841001464100242410022431002282900222290022425002501900230190024415002600d001480d001440d0026009002500900248090024209002300900228090022209002180900212090020a0900e5e0a00e3e0a00a0023006001f)) (C 0 (C 32 (M 2 0x1282900220290022025002301900324150010c15002601100250110024411002421100230110012411002221100114110021211003180d0010c0d00260090025009002420900128090022209001180900e5e1200e3e12) (M 8 0x8505100842510034849003504100844410154041003483100524310014c2900840290072029008402500f601900122190073015001201501660110055011008441100842110083011008241100722110081211008480d008400d00e680900148090013009008220900818090080a090385e120383e12)) (M 2 0x13049002424500130290012c290042825002601900250190024415002181500260110025011002441100242110023011003241100222110021411002180d002080d00e5e0200e3e0200a002f00a002b00a0017))) (C 0 (C 6 (C 4 (M 3 0x340490034445002404500642410084041001203100240290012229004602500228250066015003480d001320d002180d00962090025209001500900230090012a090046005005500500348050034405004300500428050032405003180500314050155e060153e06) (W 0x44041001203100222250046211001601100150110014411003321100124110011411001280d001080d00508090056005001500500148050014405002300500128050012405001180500114050075e060073e06)) (W 0x14c4900148410024041001201d00242190024019002221900120190021219002461100130110011411002600d0016009001500900140090012a090011a090016005001500500148050034405001300500228050012405002180500114050020c050075e060073e06)) (M 2 0x122310012229001182900228250022425002221900244150023015002500d002480d0026005002500500248050024405002300500228050022405002180500214050020c0500e5e0200e3e0200a001300a000f00a000700a0003))) (C 0 (C 40 (C 1 (M 2 0x1444100420390014825002242500260210024821002442100a402100228210022421002222100430190011415002101500260110014411002421100222110031411002200d001180d001100d001480900242090022809003180900112090010a0900e5e2200e3e22) (M 2 0x260210014a21002482100146210024421002422100a402100228210022421004222100a202100210190041415001421100832110011611001420d001300d0021a0d0073209003100900260050024805002440500d300500228050022405004180500314050020c0500e5e0600e3e06)) (C 34 (M 24 0x2b5261018505101d50490135045005404503d58410155241018484100d203500b60310185029030502502560210184821028422101828210132421018222101b50190151019060501503d501100842110031411030500d0734009005300900d70050251805015140503008050a85e220a83e22) (C 4 (W 0x4544100142410014431001222900444250016021001482100544210014221001282100124210012221002501900114150011015002300d001600900148090012809001180900112090014405001240500310050075e220073e22) (W 0x1445100440410012829001202900168210016021007442100142210012c210013819001221900244150026411002601100454110015011003441100142110023011002241100122110011211001180d001080d00360090011809001120900254050024c0500144050075e120073e12)))) (M 2 0x250450024431002482900242290026025002282500260210024821002442100242210022821002242100222210012419002101900230150021015001240d002180d0010c0d00e5e0200e3e0200a003700a003300a002700a001b00a000b)))
def cp_29_5 : CertItem := CI (some (BV 0x1700001400001400001100001400001100001100000e00001400001100001100000e00001100000e00000e00000b00001400001100001100000e00001100000e00000e00000b00001100000e00000e00000b00000e00000b00000b00000800001400001100001100000e00001100000e00000e00000b00001100000e00000e00000b00000e00000b00000b00000800001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b000008000008000005 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 896 768)) 0 0x8000000000000000 e0 (C 0 (M 2 0x1441100242110021411002100d0026009002220900212090020a090022805002240500218050020c050025ea20025e920015e8a0085e820023e620083e420063e220035e12) (C 4 (W 0x1202500160210014421001422100120190011015001400d001500900148090013009001220900128050012405001180500114050085e020083e02) (W 0x12021001201900110190014015001601100150110014411001421100230110012411001221100114110011211002100d00148090030809001280500118050020c050085e020083e02)))
def cp_29_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x33e0a0033e060035e020033e02)
def wVec_30 : Fin 5 → ℕ := ![3,3,3,3,3]
def fastW_30 (m : ℕ) : ℕ := cond (bitAt m 0) 3 0 + cond (bitAt m 1) 3 0 + cond (bitAt m 2) 3 0 + cond (bitAt m 3) 3 0 + cond (bitAt m 4) 3 0
def cFn_30 (k i : ℕ) : ℕ × ℕ := (fastW_30 i + 1 * k, 11)
def rowZ_30 : ℕ → List ℕ
  | 0 => (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 20 0xf0e0c0819151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 6 0x110905030201)
  | 3 => [0]
  | _ => []
def rowO_30 : ℕ → List ℕ
  | 0 => (unpackBytes 2 0x2010)
  | _ => []
def rowFl_30 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x1614)
  | 1 => (unpackForbs 25 0x15130000000000001912000000000000150d000000000000190b000000000000130b0000000000000d0b000000000000190a000000000000120a0000000000000d0a0000000000000b0a000000000000150700000000000013070000000000000d070000000000000b07000000000000150600000000000012060000000000000d060000000000000a060000000000000706000000000000130400000000000012040000000000000b040000000000000a0400000000000007040000000000000604)
  | 2 => (unpackForbs 10 0x1109000000000000110500000000000009050000000000001103000000000000090300000000000005030000000000001102000000000000090200000000000005020000000000000302)
  | 3 => (unpackForbs 26 0x191500000000000019130000000000001513000000000000191200000000000015120000000000001312000000000000190d000000000000150d000000000000190b000000000000130b0000000000000d0b000000000000190a000000000000120a0000000000000d0a0000000000000b0a00000000000013070000000000000d0700000000000012060000000000000a060000000000000706000000000000130400000000000012040000000000000b040000000000000a0400000000000007040000000000000604)
  | 4 => (unpackForbs 10 0x1109000000000000110500000000000009050000000000001103000000000000090300000000000005030000000000001102000000000000090200000000000005020000000000000302)
  | _ => []
def rowFbs_30 : ℕ → List (List ℕ)
  | 1 => (rowFl_30 0)
  | 2 => (rowFl_30 1)
  | 3 => (rowFl_30 2) ++ (rowFl_30 3)
  | 4 => (rowFl_30 4)
  | _ => []
def cp_30_0 : CertItem := CI none 0x177f7ffe 0x80008000 e0 (W 0)
def cp_30_1 : CertItem := CI none 0x1177fff 0x80000000 (fl 0x1614) (W 0x10003)
def cp_30_2 : CertItem := CI (some (BV 0x1100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b00000800000800000500000e00000b00000b00000800000b00000800000800000500000b000008000008000005000008000005000005000002 0xb00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b 304 352)) 0x10117 0x80000000 (N (N (N (N (N (fl 0x604) (fl 0xd0a)) (N (fl 0xd06) (fl 0x1513))) (N (N (fl 0x1204) (fl 0x130b)) (N (fl 0xd07) e0))) (N (N (N (fl 0xa04) (fl 0x190a)) (N (fl 0x1506) e0)) (N (N (fl 0x706) (fl 0x150d)) (N (fl 0x1507) e0)))) (N (N (N (N (fl 0x704) (fl 0x120a)) (N (fl 0x1206) e0)) (N (N (fl 0x1304) (fl 0x190b)) (N (fl 0x1307) e0))) (N (N (N (fl 0xb04) (fl 0xd0b)) (N (fl 0xb07) e0)) (N (N (fl 0xa06) (fl 0x1912)) (N (fl 0xb0a) e0))))) (C 3 (C 5 (C 6 (C 9 (C 10 (W 0x31e320030063003005f) (W 0x31e2a00300570030053003004f)) (W 0x31e26003004b00300470030043003003f)) (W 0x31e1a0030047003003b00300370030033003002f)) (W 0x31e160030053003002b00300270030023003001f003001b)) (W 0x31e0e003005b00300170030013003000f003000b00300070030003))
def cp_30_3 : CertItem := CI (some (BV 0x1200000f00000f00000c00000f00000c00000c00000900000f00000c00000c00000900000c00000900000900000600000f00000c00000c00000900000c00000900000900000600000c000009000009000006000009000006000006000003 0xb00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b 336 352)) 1 0x80000000 (N (N (N (N (N (N (fl 770) (fl 0x1912)) (N (fl 0x706) e0)) (N (N (fl 0x1105) e0) (N (fl 0x190a) e0))) (N (N (N (fl 0x503) e0) (N (fl 0x1307) e0)) (N (N (fl 0xa04) e0) (N (fl 0x150d) e0)))) (N (N (N (N (fl 0x902) (fl 0x1913)) (N (fl 0x1206) e0)) (N (N (fl 0x604) e0) (N (fl 0x130b) e0))) (N (N (N (fl 0x1103) e0) (N (fl 0xd0a) e0)) (N (N (fl 0x1204) e0) (N (fl 0x1312) e0))))) (N (N (N (N (N (fl 0x502) (fl 0x1513)) (N (fl 0xa06) e0)) (N (N (fl 0x1109) e0) (N (fl 0xd0b) e0))) (N (N (N (fl 0x903) e0) (N (fl 0xb0a) e0)) (N (N (fl 0xb04) e0) (N (fl 0x190d) e0)))) (N (N (N (N (fl 0x1102) (fl 0x1915)) (N (fl 0xd07) e0)) (N (N (fl 0x704) e0) (N (fl 0x190b) e0))) (N (N (N (fl 0x905) e0) (N (fl 0x120a) e0)) (N (N (fl 0x1304) e0) (N (fl 0x1512) e0)))))) (C 8 (C 9 (C 1 (C 2 (C 4 (C 16 (W 0x21e160021e0e0010087001007f001007b002006f002004f) (C 3 (C 17 (C 18 (M 2 0x22029002201900220150021e320021e2a0021e1a0021e16003008f00100770010073) (W 0x21e320021e16002008b0020087002006b0020053)) (M 2 0x220190031e320031e2a0021e1a0040083004007f004007b0010067004004b)) (W 0x41e0e0020073002003f002003b0020037002002f002002b))) (M 2 0x23011002241100222110021411002080d0081e12002007b0040073002006f003004300a0023001002f001002b)) (M 2 0x230090022809002220900218090020a090081e0a002007b0020073002006f002006b0010043003002f001002b00a001b00a0013)) (M 2 0x228050022405002180500214050020c050081e06002007f002007b0020077002006f0010043001002f003002b00a000f00a000700a0003)) (M 2 0x42825004242500220250022019002121100212090020c050081e260040063004005f004005b0040057004004700600230040033001001300100070070003)) (C 3 (M 2 0x2282100224210022221002101900210150081e220020073002006f00200670020063001005f00a00270020053001004b001004700a001f00a001700a000b) (W 0x41e0e00200730050027005001f002003f002003b00200370020033002002f002002b0050017005000b)))
def cp_30_4 : CertItem := CI (some (BV 0x1300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001000000d00000d00000a00000d00000a00000a00000700000d00000a00000a00000700000a000007000007000004 0xb00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b 368 352)) 0 0x80000000 (N (N (N (N (fl 770) (fl 0x1105)) (N (fl 0x503) e0)) (N (N (fl 0x902) e0) (N (fl 0x1103) e0))) (N (N (N (fl 0x502) (fl 0x1109)) (N (fl 0x903) e0)) (N (N (fl 0x1102) e0) (N (fl 0x905) e0)))) (C 1 (C 2 (C 4 (C 8 (C 16 (M 2 0x21425001181900118150010c15002220d00a1e02) (W 0x12849001304500120310012029001202500120190012015002200d0051e02)) (M 2 0x118290011825001142500228210022421002222100210190021015003100d00a1e020080027)) (M 2 0x1181900118150010c1500230110022411002221100214110021211003080d00a1e020080023008001f)) (M 2 0x11419001140d0010c0d002300900228090022209002180900212090030a0900a1e02008001b00800170080013)) (M 2 0x11215001120d0010a0d002300500228050022405002180500214050030c0500a1e02008000f008000b00800070080003))
def cp_30_5 : CertItem := CI (some (BV 0x1400001100001100000e00001100000e00000e00000b00001100000e00000e00000b00000e00000b00000b00000800001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b000008000008000005 0xb00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b00000b 400 352)) 0 0x80000000 e0 (C 0 (W 0x31e0a0031e06) (C 1 (W 0x3101100318090061e02) (W 0x310110032009003240500318050061e02)))
def cp_30_6 : CertItem := CI none 0 0x80000000 e0 (W 0x51e02)
def cp_30_7 : CertItem := CI none 0 0x80000000 e0 (W 0x41e02)
def wVec_31 : Fin 6 → ℕ := ![3,3,3,3,3,3]
def fastW_31 (m : ℕ) : ℕ := cond (bitAt m 0) 3 0 + cond (bitAt m 1) 3 0 + cond (bitAt m 2) 3 0 + cond (bitAt m 3) 3 0 + cond (bitAt m 4) 3 0 + cond (bitAt m 5) 3 0
def cFn_31 (k i : ℕ) : ℕ × ℕ := (fastW_31 i + 1 * k, 12)
def rowZ_31 : ℕ → List ℕ
  | 0 => (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302)
  | 1 => (unpackBytes 30 0x333224140f0e0c0831292523222119151312110d0b0a0907060504030201)
  | 2 => (unpackBytes 7 0x21110905030201)
  | 3 => [0]
  | _ => []
def rowFl_31 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 1 0x1716)
  | 1 => (unpackForbs 53 0x31250000000000003122000000000000232200000000000031190000000000002919000000000000311500000000000025150000000000001915000000000000311300000000000023130000000000001913000000000000151300000000000031120000000000002212000000000000191200000000000015120000000000001312000000000000290d000000000000250d000000000000190d000000000000150d000000000000290b000000000000230b000000000000190b000000000000130b0000000000000d0b000000000000290a000000000000220a000000000000190a000000000000120a0000000000000d0a0000000000000b0a00000000000025070000000000002307000000000000150700000000000013070000000000000d070000000000000b0700000000000025060000000000002206000000000000150600000000000012060000000000000d060000000000000a06000000000000070600000000000023040000000000002204000000000000130400000000000012040000000000000b040000000000000a0400000000000007040000000000000604)
  | 2 => (unpackForbs 28 0x353300000000000033320000000000002d2b000000000000352700000000000035260000000000002726000000000000322400000000000035170000000000003317000000000000321600000000000017160000000000003314000000000000321400000000000017140000000000001614000000000000270f000000000000170f0000000000002d0e0000000000002a0e0000000000001d0e0000000000001a0e000000000000160e000000000000240c0000000000001b0c0000000000002708000000000000260800000000000024080000000000001708)
  | 3 => (unpackForbs 39 0x3331000000000000323100000000000032220000000000001d190000000000001b1900000000000035150000000000001d15000000000000161500000000000033130000000000001b13000000000000171300000000000014130000000000003212000000000000161200000000000014120000000000002d0d0000000000001d0d0000000000000f0d0000000000000e0d0000000000002b0b0000000000001b0b0000000000000f0b0000000000000c0b0000000000002a0a0000000000001a0a0000000000000e0a0000000000000c0a000000000000270700000000000017070000000000000f070000000000000807000000000000260600000000000016060000000000000e060000000000000806000000000000240400000000000014040000000000000c040000000000000804)
  | 4 => (unpackForbs 14 0x21110000000000002109000000000000210500000000000011050000000000000905000000000000210300000000000011030000000000000903000000000000050300000000000021020000000000001102000000000000090200000000000005020000000000000302)
  | 5 => (unpackForbs 9 0x3112000000000000131200000000000023070000000000001307000000000000220600000000000007060000000000000a0400000000000007040000000000000604)
  | 6 => (unpackForbs 19 0x19110000000000001311000000000000121100000000000019090000000000000d090000000000000b090000000000000a0900000000000015050000000000000d050000000000000705000000000000060500000000000013030000000000000b030000000000000703000000000000040300000000000022020000000000000a0200000000000006020000000000000402)
  | 7 => (unpackForbs 6 0x110900000000000005030000000000001102000000000000090200000000000005020000000000000302)
  | 8 => (unpackForbs 6 0x210100000000000011010000000000000901000000000000050100000000000003010000000000000201)
  | _ => []
def rowFbs_31 : ℕ → List (List ℕ)
  | 1 => (rowFl_31 0)
  | 2 => (rowFl_31 1) ++ (rowFl_31 2) ++ (rowFl_31 3)
  | 3 => (rowFl_31 4) ++ (rowFl_31 5) ++ (rowFl_31 6)
  | 4 => (rowFl_31 7) ++ (rowFl_31 8)
  | _ => []
def cp_31_0 : CertItem := CI none 0x117177f177f7ffe 0x8000000000000000 e0 (W 0)
def cp_31_1 : CertItem := CI none 0x7011f011f7fff 0x8000000000000000 (fl 0x1716) (W 0x21eaa0021ea6002669a00266960021e72002666a00266660011e5a0011e560010003)
def cp_31_2 : CertItem := CI (some (BV 0x1400001100001100000e00001100000e00000e00000b00001100000e00000e00000b00000e00000b00000b00000800001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b00000800000800000500001100000e00000e00000b00000e00000b00000b00000800000e00000b00000b00000800000b00000800000800000500000e00000b00000b00000800000b00000800000800000500000b000008000008000005000008000005000005000002 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 704 768)) 0x100010117 0x8000000000000000 (N (N (N (N (N (N (N (fl 0x604) (fl 0x170f)) (N (fl 0x150d) (fl 0x2a0a))) (N (N (fl 0xd07) (fl 0x3533)) (N (fl 0x2919) (fl 0x1615)))) (N (N (N (fl 0x706) (fl 0x3317)) (N (fl 0x3112) (fl 0x2d0d))) (N (N (fl 0x190a) (fl 0x2606)) (N (fl 0x2708) e0)))) (N (N (N (N (fl 0x1204) (fl 0x3214)) (N (fl 0x1312) (fl 0x2b0b))) (N (N (fl 0x2507) (fl 0x2404)) (N (fl 0x3125) (fl 0x1d19)))) (N (N (N (fl 0x1506) (fl 0x3526)) (N (fl 0x3113) (fl 0x1413))) (N (N (fl 0x130b) (fl 0x2707)) (N (fl 0x1a0e) e0))))) (N (N (N (N (N (fl 0xa04) (fl 0x1614)) (N (fl 0x250d) (fl 0xf0b))) (N (N (fl 0x1507) (fl 0xc04)) (N (fl 0x2322) (fl 0x3515)))) (N (N (N (fl 0xd06) (fl 0x3224)) (N (fl 0x1913) (fl 0x1612))) (N (N (fl 0x290a) (fl 0xf07)) (N (fl 0x240c) e0)))) (N (N (N (N (fl 0x2204) (fl 0x1716)) (N (fl 0x1912) (fl 0xf0d))) (N (N (fl 0xd0a) (fl 0xe06)) (N (fl 0x2408) (fl 0x3231)))) (N (N (N (fl 0x2506) (fl 0x2d2b)) (N (fl 0x2515) (fl 0x1b13))) (N (N (fl 0x230b) (fl 0xe0a)) (N (fl 0x2a0e) e0)))))) (N (N (N (N (N (N (fl 0x704) (fl 0x270f)) (N (fl 0x190d) (fl 0xc0b))) (N (N (fl 0x1307) (fl 0x804)) (N (fl 0x3119) (fl 0x1d15)))) (N (N (N (fl 0xa06) (fl 0x3517)) (N (fl 0x1513) (fl 0x1412))) (N (N (fl 0x220a) (fl 0x807)) (N (fl 0x1b0c) e0)))) (N (N (N (N (fl 0x1304) (fl 0x3314)) (N (fl 0x1512) (fl 0xe0d))) (N (N (fl 0xb0a) (fl 0x806)) (N (fl 0x1708) (fl 0x3222)))) (N (N (N (fl 0x2206) (fl 0x3527)) (N (fl 0x1915) (fl 0x1713))) (N (N (fl 0x190b) (fl 0xc0a)) (N (fl 0x1d0e) e0))))) (N (N (N (N (N (fl 0xb04) (fl 0x1714)) (N (fl 0x290d) (fl 0x1b0b))) (N (N (fl 0x2307) (fl 0x1404)) (N (fl 0x3122) (fl 0x1b19)))) (N (N (N (fl 0x1206) (fl 0x2726)) (N (fl 0x2313) (fl 0x3212))) (N (N (fl 0xd0b) (fl 0x1707)) (N (fl 0x160e) e0)))) (N (N (N (N (fl 0x2304) (fl 0x3216)) (N (fl 0x2212) (fl 0x1d0d))) (N (N (fl 0x120a) (fl 0x1606)) (N (fl 0x2608) (fl 0x3331)))) (N (N (N (fl 0xb07) (fl 0x3332)) (N (fl 0x3115) (fl 0x3313))) (N (N (fl 0x290b) (fl 0x1a0a)) (N (fl 0x2d0e) e0))))))) (C 3 (C 5 (C 6 (C 9 (C 10 (C 12 (C 17 (C 18 (C 20 (C 24 (M 2 0x266aa00266a600666a20021ea2002669a0011e9600766920011e920021e8e004668a0041e8a0021e720021e6a0021e660021e560021e4e0021e3a0021e2e001661e001014300101db00101d700700cf0010127001012300200ff00100df) (W 0x466920031e8a00266860021e8600566620051e620011e3a0011e1e00400c700400c300101d300101cf001011b00100f300100eb)) (W 0x466a20031e8a00266860021e86001666200566520051e520011e3a0011e1e00101cb00400bf00400bb00101c700300b700101c3001010f00100e7)) (W 0x466a2001669600466920041e860016666002664a0051e4a0011e3a0011e2e00400b300400af00101bb00400ab00101b700400a700101b300100ef00100db)) (W 0x366a2001669600466920011e8e0041e8a001666a001666600266460051e460011e3a0011e2e00400a3004009f004009b00101ab004009700101a7004009300100f700100d7)) (M 2 0x2223100266e200266d200266aa00266a6002669a00266960071e8a00466860031e86002666a0021e66002665a0021e560021e4e0041e4a0041e32002662e002661e002012b00100cb00201bf00200b300600a300201a3008008f008008b002019f00800870080083002019b0020197)) (M 2 0x466920041e920021e8e00466860041e860021e720021e660021e5a00666520021e520021e4e00a662a0041e2a001012f002011f00800a300200fb0020193008007f008007b002018f00800770080073002018b008006f002018700100e300100df)) (M 2 0x466920041e920021e8e004668a0041e8a0021e720021e6a0021e5a001665600566520031e520011e4e00a66260041e26002013b001010b00800b300201070020183008006b0080067002017f0080063008005f002017b008005b0020177008005700200df)) (M 2 0x266e20021eb20021eaa0021e8e00466860041e860021e720021e6a002666600466620041e620021e56002662e00a661a0041e1a00101db0020133002011700101af00700a300200fb008006b00201730080053008004f002016f008004b0080047002016b0080043008003f0020167)) (M 2 0x266e200166c600266c20021eb20021eaa0021ea600466a20041ea20021e720021e6a0021e6600466620041e62001664e00a66160041e160020137001011300201bf00600b3002010300200eb008007b0020163008003b0080037002015f0080033008002f002015b008002b008002700201570080023)) (M 2 0x2300d004280d00266e200266d20021eb20021eaa0021ea600666a20021e9a0021e960021e720021e6a00266660061e62002665a00266560046652004660e0041e0e001013f00101df00101db00600d3002008f002008b002019b00201970020153008001f008001b002014f00800170080013002014b008000f008000b002014700800070080003))
def cp_31_3 : CertItem := CI (some (BV 0x1500001200001200000f00001200000f00000f00000c00001200000f00000f00000c00000f00000c00000c00000900001200000f00000f00000c00000f00000c00000c00000900000f00000c00000c00000900000c00000900000900000600001200000f00000f00000c00000f00000c00000c00000900000f00000c00000c00000900000c00000900000900000600000f00000c00000c00000900000c00000900000900000600000c000009000009000006000009000006000006000003 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 768 768)) 1 0x8000000000000000 (N (N (N (N (N (N (fl 770) (fl 0x705)) (N (fl 0xa04) e0)) (N (N (fl 0x2103) (fl 0x1311)) (N (fl 0x602) e0))) (N (N (N (fl 0x2102) (fl 0xb09)) (N (fl 0x2307) e0)) (N (N (fl 0x2109) e0) (N (fl 0x703) e0)))) (N (N (N (N (fl 0x902) (fl 0x1505)) (N (fl 0x2206) e0)) (N (N (fl 0x1105) e0) (N (fl 0x2202) e0))) (N (N (N (fl 0x903) (fl 0x1909)) (N (fl 0x3112) e0)) (N (N (fl 0x604) e0) (N (fl 0x1303) e0))))) (N (N (N (N (N (fl 0x502) (fl 0xd05)) (N (fl 0x706) e0)) (N (N (fl 0x905) (fl 0x1911)) (N (fl 0xa02) e0))) (N (N (N (fl 0x503) (fl 0xd09)) (N (fl 0x1312) e0)) (N (N (fl 0x2111) e0) (N (fl 0xb03) e0)))) (N (N (N (N (fl 0x1102) (fl 0xa09)) (N (fl 0x1307) e0)) (N (N (fl 0x2105) e0) (N (fl 0x403) e0))) (N (N (N (fl 0x1103) (fl 0x1211)) (N (fl 0x402) e0)) (N (N (fl 0x704) e0) (N (fl 0x605) e0)))))) (C 1 (C 2 (C 4 (C 8 (C 16 (C 32 (M 2 0x61ea200666920061e8a00666860061e6200666520031e4a0031e460061e32006662a006662600300570030047003003f003003b) (W 0x366a2003669200366820061e820031e6200366520031e4a0031e32003662a003005b0030053003004b0030043)) (W 0x31e8a0031e86003665200366420061e420031e32003662a0036626003661a006003700300a700300a3003009f003003b)) (W 0x366920031e8a0031e8600366520031e4600366420031e4200666220031e220060033003009b00300970030093003008f003004f003003b)) (W 0x31e8a0031e8600266620021e620031e4a00266460011e46003662a00666120031e12001660e006002f003008b006002b003008700600270030083003007f0020043)) (W 0x366920031e8a0031e8600366620031e520031e4600366260036616003660a0031e0a0060023003007b006001f0030077006001b00300730060017003006f)) (W 0x31e920031e8a003666200366520031e4a0031e46003662a003661a00366060031e06003006b0060013006000f0030067006000b00300630060007003005f0060003))
def cp_31_4 : CertItem := CI (some (BV 0x1600001300001300001000001300001000001000000d00001300001000001000000d00001000000d00000d00000a00001300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001300001000001000000d00001000000d00000d00000a00001000000d00000d00000a00000d00000a00000a00000700001000000d00000d00000a00000d00000a00000a00000700000d00000a00000a00000700000a000007000007000004 0xc00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c00000c 832 768)) 0 0x8000000000000000 (N (N (N (N (fl 770) (fl 0x501)) (N (fl 0x503) e0)) (N (N (fl 0x902) (fl 0x1101)) (N (fl 513) e0))) (N (N (N (fl 0x502) (fl 0x901)) (N (fl 0x1109) e0)) (N (N (fl 0x1102) (fl 0x2101)) (N (fl 769) e0)))) (C 0 (C 1 (M 2 0x26009002500900466920041e8a0041e8600466820061e8200466620041e520041e4a0041e460021e420041e32004662a00466260026622004661a004661600266120031e12003660e0011e0e001660a00800170050013) (W 0x21e860051e82002666200266520021e4a0021e460031e42002662a00266260016622002661a002661600466060041e06002000f004000b00400070050003)) (W 0x21e8a0021e860031e82002666200266520021e4a0021e460031e42002662a00266260016622002661a0026616001661200466020041e02002002f002002b00400270040023005001f005001b))
def cp_31_5 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x11e860041e820011e620011e520011e4a0011e460041e42001662a00166260046622001661a001661600466120031e0600566020021e02)
def cp_31_6 : CertItem := CI none 0 0x8000000000000000 e0 (W 0x3662200366120031e0a0031e060066602)
def wVec_32 : Fin 4 → ℕ := ![5,5,5,5]
def fastW_32 (m : ℕ) : ℕ := cond (bitAt m 0) 5 0 + cond (bitAt m 1) 5 0 + cond (bitAt m 2) 5 0 + cond (bitAt m 3) 5 0
def cFn_32 (k i : ℕ) : ℕ × ℕ := (fastW_32 i + 2 * k, 18)
def rowZ_32 : ℕ → List ℕ
  | 0 => (unpackBytes 14 0xf0e0d0c0b0a0908070605040302)
  | 2 => (unpackBytes 11 0xd0b0a0706040905030201)
  | 3 => [0]
  | _ => []
def rowFl_32 : ℕ → List (List ℕ)
  | 0 => (unpackForbs 6 0x90500000000000009030000000000000503000000000000090200000000000005020000000000000302)
  | 1 => (unpackForbs 3 0xb0a00000000000007060000000000000704)
  | 2 => (unpackForbs 12 0xd090000000000000b090000000000000a090000000000000d05000000000000070500000000000006050000000000000b03000000000000070300000000000004030000000000000a0200000000000006020000000000000402)
  | 3 => (unpackForbs 2 0x5030000000000000902)
  | 4 => (unpackForbs 4 0x901000000000000050100000000000003010000000000000201)
  | _ => []
def rowFbs_32 : ℕ → List (List ℕ)
  | 3 => (rowFl_32 0) ++ (rowFl_32 1) ++ (rowFl_32 2)
  | 4 => (rowFl_32 3) ++ (rowFl_32 4)
  | _ => []
def cp_32_0 : CertItem := CI none 0x7ffe 0x8000 e0 (W 0)
def cp_32_2 : CertItem := CI none 0x177f 0x8000 e0 (W 0)
def cp_32_3 : CertItem := CI (some (BV 0x1a00001500001500001000001500001000001000000b00001500001000001000000b00001000000b00000b000006 0x12000012000012000012000012000012000012000012000012000012000012000012000012000012000012000012 256 288)) 1 0x8000 (N (N (N (N (N (fl 770) (fl 0x705)) (N (fl 0xb0a) e0)) (N (N (fl 0x903) (fl 0xd09)) (N (fl 0x403) e0))) (N (N (N (fl 0x902) (fl 0xa09)) (N (fl 0x602) e0)) (N (N (fl 0x704) e0) (N (fl 0xb03) e0)))) (N (N (N (N (fl 0x502) (fl 0xd05)) (N (fl 0x402) e0)) (N (N (fl 0x905) e0) (N (fl 0x703) e0))) (N (N (N (fl 0x503) (fl 0xb09)) (N (fl 0xa02) e0)) (N (N (fl 0x706) e0) (N (fl 0x605) e0))))) (C 1 (C 2 (C 4 (C 8 (W 0x20023001001f001001b) (W 0x210190021015002100d0020053002004f002004b)) (W 0x214110021211002080d002004700700170020043002003f)) (W 0x2180900212090020a09002003b00700130020037007000f0020033)) (W 0x2180500214050020c05002002f007000b002002b007000700200270070003))
def cp_32_4 : CertItem := CI (some (BV 0x1c00001700001700001200001700001200001200000d00001700001200001200000d00001200000d00000d000008 0x12000012000012000012000012000012000012000012000012000012000012000012000012000012000012000012 288 288)) 0 0x8000 (N (N (N (fl 0x902) (fl 0x501)) (N (fl 513) e0)) (N (N (fl 0x503) (fl 0x901)) (N (fl 769) e0))) (C 0 (W 0x500070050003) (W 0x500170050013005000f005000b))
def cp_32_5 : CertItem := CI (some (BV 0x1e00001900001900001400001900001400001400000f00001900001400001400000f00001400000f00000f00000a 0x12000012000012000012000012000012000012000012000012000012000012000012000012000012000012000012 320 288)) 0 0x8000 e0 (C 1 (M 2 0x3101100310090030809) (M 2 0x1101100110090010809004100500408050040405))
def cp_32_6 : CertItem := CI none 0 0x8000 e0 (W 0)
def cp_32_7 : CertItem := CI none 0 0x8000 e0 (W 0)
def cp_32_8 : CertItem := CI none 0 0x8000 e0 (W 0)

theorem cert_7_0 : checkCertItem 64 0 (cFn_7 0) 0 0 0x8888888088808001 [] (rowZ_7 0) (rowO_7 0) cp_7_0 = true := by
  decide +kernel

theorem cert_7_1 : checkCertItem 64 0 (cFn_7 1) 0 0 0x8888888088808001 [] (rowZ_7 1) [63] cp_7_1 = true := by
  decide +kernel

theorem cert_7_2 : checkCertItem 64 0 (cFn_7 2) 0 0 0x8888888088808001 [] (rowZ_7 2) [63] cp_7_2 = true := by
  decide +kernel

theorem cert_7_3 : checkCertItem 64 0 (cFn_7 3) 0 0 0x8888888088808001 [] (rowZ_7 3) [63] cp_7_3 = true := by
  decide +kernel

theorem cert_7_4 : checkCertItem 64 0 (cFn_7 4) 0 0 0x8888888088808001 [] [] [63] cp_7_4 = true := by
  decide +kernel

theorem cert_7_5 : checkCertItem 64 0 (cFn_7 5) 0 0 0x8888888088808001 [] [] [63] cp_7_5 = true := by
  decide +kernel

theorem cert_7_6 : checkCertItem 64 0 (cFn_7 6) 0 0 0x8888888088808001 [] [] [63] cp_7_6 = true := by
  decide +kernel

theorem cert_8_0 : checkCertItem 128 0 (cFn_8 0) 0 0 0x80808080808080808080808080808001 [] (rowZ_8 0) (rowO_8 0) cp_8_0 = true := by
  decide +kernel

theorem cert_8_1 : checkCertItem 128 5 (cFn_8 1) 0 0 0x80808080808080808080808080808001 (rowFbs_8 1) (rowZ_8 1) [127] cp_8_1 = true := by
  decide +kernel

theorem cert_8_2 : checkCertItem 128 5 (cFn_8 2) 0 0 0x80808080808080808080808080808001 (rowFbs_8 2) (rowZ_8 2) [127] cp_8_2 = true := by
  decide +kernel

theorem cert_8_3 : checkCertItem 128 0 (cFn_8 3) 0 0 0x80808080808080808080808080808001 [] (rowZ_8 3) [127] cp_8_3 = true := by
  decide +kernel

theorem cert_8_4 : checkCertItem 128 0 (cFn_8 4) 0 0 0x80808080808080808080808080808001 [] [] [127] cp_8_4 = true := by
  decide +kernel

theorem cert_8_5 : checkCertItem 128 0 (cFn_8 5) 0 0 0x80808080808080808080808080808001 [] [] [127] cp_8_5 = true := by
  decide +kernel

theorem cert_12_0 : checkCertItem 64 0 (cFn_12 0) 0 0 0x8080808080808001 [] (rowZ_12 0) (rowO_12 0) cp_12_0 = true := by
  decide +kernel

theorem cert_12_1 : checkCertItem 64 0 (cFn_12 1) 0 0 0x8080808080808001 [] (rowZ_12 1) [63] cp_12_1 = true := by
  decide +kernel

theorem cert_12_2 : checkCertItem 64 4 (cFn_12 2) 0 0 0x8080808080808001 (rowFbs_12 2) (rowZ_12 2) [63] cp_12_2 = true := by
  decide +kernel

theorem cert_12_3 : checkCertItem 64 4 (cFn_12 3) 0 0 0x8080808080808001 (rowFbs_12 3) (rowZ_12 3) [63] cp_12_3 = true := by
  decide +kernel

theorem cert_12_4 : checkCertItem 64 0 (cFn_12 4) 0 0 0x8080808080808001 [] [] [63] cp_12_4 = true := by
  decide +kernel

theorem cert_12_5 : checkCertItem 64 0 (cFn_12 5) 0 0 0x8080808080808001 [] [] [63] cp_12_5 = true := by
  decide +kernel

theorem cert_12_6 : checkCertItem 64 0 (cFn_12 6) 0 0 0x8080808080808001 [] [] [63] cp_12_6 = true := by
  decide +kernel

theorem cert_16_0 : checkCertItem 32 0 (cFn_16 0) 0 2 0x88808001 [] (rowZ_16 0) (rowO_16 0) cp_16_0 = true := by
  decide +kernel

theorem cert_16_1 : checkCertItem 32 0 (cFn_16 1) 0 0 0x88808001 [] (rowZ_16 1) [31] cp_16_1 = true := by
  decide +kernel

theorem cert_16_2 : checkCertItem 32 3 (cFn_16 2) 0 0 0x88808001 (rowFbs_16 2) (rowZ_16 2) [31] cp_16_2 = true := by
  decide +kernel

theorem cert_16_3 : checkCertItem 32 4 (cFn_16 3) 0 0 0x88808001 (rowFbs_16 3) (rowZ_16 3) [31] cp_16_3 = true := by
  decide +kernel

theorem cert_16_4 : checkCertItem 32 0 (cFn_16 4) 0 0 0x88808001 [] [] [31] cp_16_4 = true := by
  decide +kernel

theorem cert_16_5 : checkCertItem 32 0 (cFn_16 5) 0 0 0x88808001 [] [] [31] cp_16_5 = true := by
  decide +kernel

theorem cert_16_6 : checkCertItem 32 0 (cFn_16 6) 0 0 0x88808001 [] [] [31] cp_16_6 = true := by
  decide +kernel

theorem cert_16_7 : checkCertItem 32 0 (cFn_16 7) 2 0 0x88808001 [] [] [31] cp_16_7 = true := by
  decide +kernel

theorem cert_26_0 : checkCertItem 64 2 (cFn_26 0) 0 0 0x8000800080808001 (rowFbs_26 0) (rowZ_26 0) (rowO_26 0) cp_26_0 = true := by
  decide +kernel

theorem cert_26_1 : checkCertItem 64 6 (cFn_26 1) 0 0 0x8000800080808001 (rowFbs_26 1) (rowZ_26 1) [63] cp_26_1 = true := by
  decide +kernel

theorem cert_26_2 : checkCertItem 64 7 (cFn_26 2) 0 0 0x8000800080808001 (rowFbs_26 2) (rowZ_26 2) [63] cp_26_2 = true := by
  decide +kernel

theorem cert_26_3 : checkCertItem 64 5 (cFn_26 3) 0 0 0x8000800080808001 (rowFbs_26 3) (rowZ_26 3) [63] cp_26_3 = true := by
  decide +kernel

theorem cert_26_4 : checkCertItem 64 0 (cFn_26 4) 0 0 0x8000800080808001 [] [] [63] cp_26_4 = true := by
  decide +kernel

theorem cert_26_5 : checkCertItem 64 0 (cFn_26 5) 0 0 0x8000800080808001 [] [] [63] cp_26_5 = true := by
  decide +kernel

theorem cert_26_6 : checkCertItem 64 0 (cFn_26 6) 0 0 0x8000800080808001 [] [] [63] cp_26_6 = true := by
  decide +kernel

theorem cert_27_0 : checkCertItem 64 0 (cFn_27 0) 0 7 0x8000800080008001 (rowFbs_27 0) (rowZ_27 0) (rowO_27 0) cp_27_0 = true := by
  decide +kernel

theorem cert_27_1 : checkCertItem 64 7 (cFn_27 1) 0 0 0x8000800080008001 (rowFbs_27 1) (rowZ_27 1) [63] cp_27_1 = true := by
  decide +kernel

theorem cert_27_2 : checkCertItem 64 9 (cFn_27 2) 0 0 0x8000800080008001 (rowFbs_27 2) (rowZ_27 2) [63] cp_27_2 = true := by
  decide +kernel

theorem cert_27_3 : checkCertItem 64 8 (cFn_27 3) 0 0 0x8000800080008001 (rowFbs_27 3) (rowZ_27 3) [63] cp_27_3 = true := by
  decide +kernel

theorem cert_27_4 : checkCertItem 64 0 (cFn_27 4) 0 0 0x8000800080008001 [] [] [63] cp_27_4 = true := by
  decide +kernel

theorem cert_27_5 : checkCertItem 64 0 (cFn_27 5) 0 0 0x8000800080008001 [] [] [63] cp_27_5 = true := by
  decide +kernel

theorem cert_27_6 : checkCertItem 64 0 (cFn_27 6) 7 0 0x8000800080008001 [] [] [63] cp_27_6 = true := by
  decide +kernel

theorem cert_28_0 : checkCertItem 32 0 (cFn_28 0) 0 5 0x80808001 [] (rowZ_28 0) (rowO_28 0) cp_28_0 = true := by
  decide +kernel

theorem cert_28_1 : checkCertItem 32 0 (cFn_28 1) 0 0 0x80808001 (rowFbs_28 1) (rowZ_28 1) [31] cp_28_1 = true := by
  decide +kernel

theorem cert_28_2 : checkCertItem 32 6 (cFn_28 2) 0 0 0x80808001 (rowFbs_28 2) (rowZ_28 2) [31] cp_28_2 = true := by
  decide +kernel

theorem cert_28_3 : checkCertItem 32 7 (cFn_28 3) 0 0 0x80808001 (rowFbs_28 3) (rowZ_28 3) [31] cp_28_3 = true := by
  decide +kernel

theorem cert_28_4 : checkCertItem 32 3 (cFn_28 4) 0 0 0x80808001 (rowFbs_28 4) [] [31] cp_28_4 = true := by
  decide +kernel

theorem cert_28_5 : checkCertItem 32 0 (cFn_28 5) 0 0 0x80808001 [] [] [31] cp_28_5 = true := by
  decide +kernel

theorem cert_28_6 : checkCertItem 32 0 (cFn_28 6) 0 0 0x80808001 [] [] [31] cp_28_6 = true := by
  decide +kernel

theorem cert_28_7 : checkCertItem 32 0 (cFn_28 7) 5 0 0x80808001 [] [] [31] cp_28_7 = true := by
  decide +kernel

theorem cert_29_0 : checkCertItem 64 0 (cFn_29 0) 0 0 0x8000800080000001 [] (rowZ_29 0) (rowO_29 0) cp_29_0 = true := by
  decide +kernel

theorem cert_29_1 : checkCertItem 64 7 (cFn_29 1) 0 0 0x8000800080000001 (rowFbs_29 1) (rowZ_29 1) [63] cp_29_1 = true := by
  decide +kernel

theorem cert_29_2 : checkCertItem 64 7 (cFn_29 2) 0 0 0x8000800080000001 (rowFbs_29 2) (rowZ_29 2) [63] cp_29_2 = true := by
  decide +kernel

theorem cert_29_3 : checkCertItem 64 7 (cFn_29 3) 0 0 0x8000800080000001 (rowFbs_29 3) (rowZ_29 3) [63] cp_29_3 = true := by
  decide +kernel

theorem cert_29_4 : checkCertItem 64 4 (cFn_29 4) 0 0 0x8000800080000001 (rowFbs_29 4) [] [63] cp_29_4 = true := by
  decide +kernel

theorem cert_29_5 : checkCertItem 64 0 (cFn_29 5) 0 0 0x8000800080000001 [] [] [63] cp_29_5 = true := by
  decide +kernel

theorem cert_29_6 : checkCertItem 64 0 (cFn_29 6) 0 0 0x8000800080000001 [] [] [63] cp_29_6 = true := by
  decide +kernel

theorem cert_30_0 : checkCertItem 32 0 (cFn_30 0) 0 6 0x80008001 [] (rowZ_30 0) (rowO_30 0) cp_30_0 = true := by
  decide +kernel

theorem cert_30_1 : checkCertItem 32 0 (cFn_30 1) 0 0 0x80008001 (rowFbs_30 1) (rowZ_30 1) [31] cp_30_1 = true := by
  decide +kernel

theorem cert_30_2 : checkCertItem 32 5 (cFn_30 2) 0 0 0x80008001 (rowFbs_30 2) (rowZ_30 2) [31] cp_30_2 = true := by
  decide +kernel

theorem cert_30_3 : checkCertItem 32 6 (cFn_30 3) 0 0 0x80008001 (rowFbs_30 3) (rowZ_30 3) [31] cp_30_3 = true := by
  decide +kernel

theorem cert_30_4 : checkCertItem 32 4 (cFn_30 4) 0 0 0x80008001 (rowFbs_30 4) [] [31] cp_30_4 = true := by
  decide +kernel

theorem cert_30_5 : checkCertItem 32 0 (cFn_30 5) 0 0 0x80008001 [] [] [31] cp_30_5 = true := by
  decide +kernel

theorem cert_30_6 : checkCertItem 32 0 (cFn_30 6) 0 0 0x80008001 [] [] [31] cp_30_6 = true := by
  decide +kernel

theorem cert_30_7 : checkCertItem 32 0 (cFn_30 7) 6 0 0x80008001 [] [] [31] cp_30_7 = true := by
  decide +kernel

theorem cert_31_0 : checkCertItem 64 0 (cFn_31 0) 0 6 0x8008000000008001 [] (rowZ_31 0) [63] cp_31_0 = true := by
  decide +kernel

theorem cert_31_1 : checkCertItem 64 0 (cFn_31 1) 0 0 0x8008000000008001 (rowFbs_31 1) (rowZ_31 1) [63] cp_31_1 = true := by
  decide +kernel

theorem cert_31_2 : checkCertItem 64 7 (cFn_31 2) 0 0 0x8008000000008001 (rowFbs_31 2) (rowZ_31 2) [63] cp_31_2 = true := by
  decide +kernel

theorem cert_31_3 : checkCertItem 64 6 (cFn_31 3) 0 0 0x8008000000008001 (rowFbs_31 3) (rowZ_31 3) [63] cp_31_3 = true := by
  decide +kernel

theorem cert_31_4 : checkCertItem 64 4 (cFn_31 4) 0 0 0x8008000000008001 (rowFbs_31 4) [] [63] cp_31_4 = true := by
  decide +kernel

theorem cert_31_5 : checkCertItem 64 0 (cFn_31 5) 0 0 0x8008000000008001 [] [] [63] cp_31_5 = true := by
  decide +kernel

theorem cert_31_6 : checkCertItem 64 0 (cFn_31 6) 6 0 0x8008000000008001 [] [] [63] cp_31_6 = true := by
  decide +kernel

theorem cert_32_0 : checkCertItem 16 0 (cFn_32 0) 0 16 0x8001 [] (rowZ_32 0) [15] cp_32_0 = true := by
  decide +kernel

theorem cert_32_2 : checkCertItem 16 0 (cFn_32 2) 0 0 0x8001 [] (rowZ_32 2) [15] cp_32_2 = true := by
  decide +kernel

theorem cert_32_3 : checkCertItem 16 5 (cFn_32 3) 0 0 0x8001 (rowFbs_32 3) (rowZ_32 3) [15] cp_32_3 = true := by
  decide +kernel

theorem cert_32_4 : checkCertItem 16 3 (cFn_32 4) 0 0 0x8001 (rowFbs_32 4) [] [15] cp_32_4 = true := by
  decide +kernel

theorem cert_32_5 : checkCertItem 16 0 (cFn_32 5) 0 0 0x8001 [] [] [15] cp_32_5 = true := by
  decide +kernel

theorem cert_32_6 : checkCertItem 16 0 (cFn_32 6) 0 0 0x8001 [] [] [15] cp_32_6 = true := by
  decide +kernel

theorem cert_32_7 : checkCertItem 16 0 (cFn_32 7) 0 0 0x8001 [] [] [15] cp_32_7 = true := by
  decide +kernel

theorem cert_32_8 : checkCertItem 16 0 (cFn_32 8) 16 0 0x8001 [] [] [15] cp_32_8 = true := by
  decide +kernel

theorem solve_7 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hcopy : HasCopy 6 mi_7 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_7 miExp_7 [(15,23),(15,39),(15,51),(23,39),(27,43)] 0x8888888088808001 wVec_7 fastW_7 1 16 0 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro _e _K _sub _D _hD v _hv _hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 6 0 hn255 (cFn_7 0) 0 0 0x8888888088808001 [] (rowZ_7 0) (rowO_7 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_7 0) (by decide +kernel)) cert_7_0
  · exact cert_step 6 0 hn255 (cFn_7 1) 0 0 0x8888888088808001 [] (rowZ_7 1) [63] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_7_1
  · exact cert_step 6 0 hn255 (cFn_7 2) 0 0 0x8888888088808001 [] (rowZ_7 2) [63] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_7_2
  · exact cert_step 6 0 hn255 (cFn_7 3) 0 0 0x8888888088808001 [] (rowZ_7 3) [63] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_7_3
  · exact cert_step 6 0 hn255 (cFn_7 4) 0 0 0x8888888088808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_7_4
  · exact cert_step 6 0 hn255 (cFn_7 5) 0 0 0x8888888088808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_7_5
  · exact cert_step 6 0 hn255 (cFn_7 6) 0 0 0x8888888088808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_7_6

theorem solve_8 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_7 : ¬ HasCopy 6 mi_7 F)
    (hcopy : HasCopy 7 mi_8 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 7 F closed empty full minSize mi_8 miExp_8 [(15,23),(15,39),(15,71),(23,39),(23,71),(39,71),(15,55),(15,87),(15,103),(23,103),(31,103)] 0x80808080808080808080808080808001 wVec_8 fastW_8 2 29 0 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 7) ≤ 255 := by decide
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 7 kv bj F e K sub hk D hD v hv 0x80808080808080808080808080808001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 7 0 hn255 (cFn_8 0) 0 0 0x80808080808080808080808080808001 [] (rowZ_8 0) (rowO_8 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 63 0x71696563626159555352514d4b4a494746454443424139353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_8 0) (by decide +kernel)) cert_8_0
  · have hfb_7 := fBat hk_eq mi_7 hno_7 (rowFl_8 0) (unpackPerms 22 0x543268005431680054306800541068005310680043106800421068006532480065423800654138006530480065403800654208006532180064213800542138006431280054312800653108006520180065210800542108) (by decide +kernel)
    exact cert_step 7 5 hn255 (cFn_8 1) 0 0 0x80808080808080808080808080808001 (rowFbs_8 1) (rowZ_8 1) [127] bit join hgens hfb_7 (exclude_list (exclude 1 hk_eq) (unpackBytes 29 0x6151494543424131292523222119151312110d0b0a0907060504030201) (by decide +kernel)) (stable_top (stable 1 hk_eq 127 (Or.inl rfl))) cert_8_1
  · have hfb_7 := fBat hk_eq mi_7 hno_7 (rowFl_8 1) (unpackPerms 30 0x6543880065428800654188006540880065328800643288005432880065318800643188005431880065308800643088005430880064218800542188006321880053218800652088006420880054208800632088004320880065108800641088005410880053108800431088006210880052108800321088) (by decide +kernel)
    exact cert_step 7 5 hn255 (cFn_8 2) 0 0 0x80808080808080808080808080808001 (rowFbs_8 2) (rowZ_8 2) [127] bit join hgens hfb_7 (exclude_list (exclude 2 hk_eq) (unpackBytes 8 0x4121110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 127 (Or.inl rfl))) cert_8_2
  · exact cert_step 7 0 hn255 (cFn_8 3) 0 0 0x80808080808080808080808080808001 [] (rowZ_8 3) [127] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 127 (Or.inl rfl))) cert_8_3
  · exact cert_step 7 0 hn255 (cFn_8 4) 0 0 0x80808080808080808080808080808001 [] [] [127] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 127 (Or.inl rfl))) cert_8_4
  · exact cert_step 7 0 hn255 (cFn_8 5) 0 0 0x80808080808080808080808080808001 [] [] [127] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 127 (Or.inl rfl))) cert_8_5

theorem solve_12 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_7 : ¬ HasCopy 6 mi_7 F)
    (hno_8 : ¬ HasCopy 7 mi_8 F)
    (hcopy : HasCopy 6 mi_12 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_12 miExp_12 [(15,23),(15,39),(23,39),(15,55)] 0x8080808080808001 wVec_12 fastW_12 2 33 0 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 6 kv bj F e K sub hk D hD v hv 0x8080808080808001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 6 kv bj F e K sub hk D hD v hv 0x8080808080808001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 6 0 hn255 (cFn_12 0) 0 0 0x8080808080808001 [] (rowZ_12 0) (rowO_12 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_12 0) (by decide +kernel)) cert_12_0
  · have hz_u_8 := uBat hk_eq mi_8 hno_8 [7] [0x5436210] (by decide +kernel)
    exact cert_step 6 0 hn255 (cFn_12 1) 0 0 0x8080808080808001 [] (rowZ_12 1) [63] bit join hgens (fun _ h => nomatch h) (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_8) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_12_1
  · have hfb_7 := fBat hk_eq mi_7 hno_7 (rowFl_12 0) [0x543276] (by decide +kernel)
    have hfb_8 := fBat hk_eq mi_8 hno_8 (rowFl_12 1) (unpackPerms 11 0x431057704210577032105770532147703210477054213770542037705410377052103770421037705410277) (by decide +kernel)
    exact cert_step 6 4 hn255 (cFn_12 2) 0 0 0x8080808080808001 (rowFbs_12 2) (rowZ_12 2) [63] bit join hgens (forbs_append hfb_7 hfb_8) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_12_2
  · have hfb_8 := fBat hk_eq mi_8 hno_8 (rowFl_12 2) (unpackPerms 15 0x54328770543187705421877053218770432187705430877054208770532087704320877054108770531087704310877052108770421087703210877) (by decide +kernel)
    exact cert_step 6 4 hn255 (cFn_12 3) 0 0 0x8080808080808001 (rowFbs_12 3) (rowZ_12 3) [63] bit join hgens hfb_8 (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_12_3
  · exact cert_step 6 0 hn255 (cFn_12 4) 0 0 0x8080808080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_12_4
  · exact cert_step 6 0 hn255 (cFn_12 5) 0 0 0x8080808080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_12_5
  · exact cert_step 6 0 hn255 (cFn_12 6) 0 0 0x8080808080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_12_6

theorem solve_16 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_12 : ¬ HasCopy 6 mi_12 F)
    (hcopy : HasCopy 5 mi_16 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 5 F closed empty full minSize mi_16 miExp_16 [(15,23)] 0x88808001 wVec_16 fastW_16 2 28 2 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 5) ≤ 255 := by decide
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 5 kv bj F e K sub hk D hD v hv 0x88808001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 5 0 hn255 (cFn_16 0) 0 2 0x88808001 [] (rowZ_16 0) (rowO_16 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_16 0) (by decide +kernel)) cert_16_0
  · exact cert_step 5 0 hn255 (cFn_16 1) 0 0 0x88808001 [] (rowZ_16 1) [31] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 1 hk_eq) (unpackBytes 16 0x19151312110d0b0a0907060504030201) (by decide +kernel)) (stable_top (stable 1 hk_eq 31 (Or.inl rfl))) cert_16_1
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_16 0) (unpackPerms 7 0x210466004213660042036600210366004312660043026600310266) (by decide +kernel)
    exact cert_step 5 3 hn255 (cFn_16 2) 0 0 0x88808001 (rowFbs_16 2) (rowZ_16 2) [31] bit join hgens hfb_12 (exclude_list (exclude 2 hk_eq) (unpackBytes 6 0x110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 31 (Or.inl rfl))) cert_16_2
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_16 1) (unpackPerms 10 0x432766004317660042176600321766004307660042076600320766004107660031076600210766) (by decide +kernel)
    exact cert_step 5 4 hn255 (cFn_16 3) 0 0 0x88808001 (rowFbs_16 3) (rowZ_16 3) [31] bit join hgens hfb_12 (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 31 (Or.inl rfl))) cert_16_3
  · exact cert_step 5 0 hn255 (cFn_16 4) 0 0 0x88808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 31 (Or.inl rfl))) cert_16_4
  · exact cert_step 5 0 hn255 (cFn_16 5) 0 0 0x88808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 31 (Or.inl rfl))) cert_16_5
  · exact cert_step 5 0 hn255 (cFn_16 6) 0 0 0x88808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 31 (Or.inl rfl))) cert_16_6
  · exact cert_step 5 0 hn255 (cFn_16 7) 2 0 0x88808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 7 hk_eq 31 (Or.inl rfl))) cert_16_7

theorem solve_26 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_12 : ¬ HasCopy 6 mi_12 F)
    (hno_16 : ¬ HasCopy 5 mi_16 F)
    (hcopy : HasCopy 6 mi_26 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_26 miExp_26 [(15,23),(23,47)] 0x8000800080808001 wVec_26 fastW_26 2 23 0 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 6 kv bj F e K sub hk D hD v hv 0x8000800080808001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 6 kv bj F e K sub hk D hD v hv 0x8000800080808001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hz_u_12 := uBat hk_eq mi_12 hno_12 [39] [0x543210] (by decide +kernel)
    have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_26 0) [0x210543] (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_26 1) (unpackPerms 2 0x5203200052131) (by decide +kernel)
    exact cert_step 6 2 hn255 (cFn_26 0) 0 0 0x8000800080808001 (rowFbs_26 0) (rowZ_26 0) (rowO_26 0) bit join hgens (forbs_append hfb_12 hfb_16) (zeros_append (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) hz_u_12) (stable_list (stable 0 hk_eq) (rowO_26 0) (by decide +kernel)) cert_26_0
  · have hz_u_12 := uBat hk_eq mi_12 hno_12 [7] [0x436210] (by decide +kernel)
    have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_26 2) (unpackPerms 9 0x2105470043251700410527003105270043051700420517003205170032150700510437) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_26 3) (unpackPerms 27 0x432570003215700042057000320570002105700054327000530470005403700054307000541270005421700010643000206420002164100052037000530270005320700043207000106330005103700053017000531070004103700043017000431070002063200021631) (by decide +kernel)
    exact cert_step 6 6 hn255 (cFn_26 1) 0 0 0x8000800080808001 (rowFbs_26 1) (rowZ_26 1) [63] bit join hgens (forbs_append hfb_12 hfb_16) (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_12) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_26_1
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_26 4) (unpackPerms 60 0x4325770043157700421577003215770043057700420577003205770041057700310577002105770053247700531477005214770032147700530477005204770032047700510477003104770021047700542377005432770054137700543177005213770042137700540377005430770052037700420377005103770041037700210377005412770054217700531277004312770053217700432177005402770054207700530277004302770053207700432077005102770041027700310277005401770054107700530177004301770053107700431077005201770042017700320177005210770042107700321077) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_26 5) (unpackPerms 18 0x543770005427700054177000540770005327700053177000530770004307700052177000421770003217700052077000420770003207700051077000410770003107700021077) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_26 2) 0 0 0x8000800080808001 (rowFbs_26 2) (rowZ_26 2) [63] bit join hgens (forbs_append hfb_12 hfb_16) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_26_2
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_26 6) (unpackPerms 20 0x54387700542877005328770043287700541877005318770043187700521877004218770032187700540877005308770043087700520877004208770032087700510877004108770031087700210877) (by decide +kernel)
    exact cert_step 6 5 hn255 (cFn_26 3) 0 0 0x8000800080808001 (rowFbs_26 3) (rowZ_26 3) [63] bit join hgens hfb_12 (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_26_3
  · exact cert_step 6 0 hn255 (cFn_26 4) 0 0 0x8000800080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_26_4
  · exact cert_step 6 0 hn255 (cFn_26 5) 0 0 0x8000800080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_26_5
  · exact cert_step 6 0 hn255 (cFn_26 6) 0 0 0x8000800080808001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_26_6

theorem solve_27 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_12 : ¬ HasCopy 6 mi_12 F)
    (hno_16 : ¬ HasCopy 5 mi_16 F)
    (hno_26 : ¬ HasCopy 6 mi_26 F)
    (hcopy : HasCopy 6 mi_27 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_27 miExp_27 [(31,47)] 0x8000800080008001 wVec_27 fastW_27 1 9 7 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 6 kv bj F e K sub hk D hD v hv 0x8000800080008001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 6 kv bj F e K sub hk D hD v hv 0x8000800080008001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hz_u_26 := uBat hk_eq mi_26 hno_26 (unpackBytes 8 0x2f2e2c281f1e1c18) (unpackPerms 8 0x45032200451321004523110045321100540322005413210054231100543211) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_27 0) [0x32054] (by decide +kernel)
    exact cert_step 6 0 hn255 (cFn_27 0) 0 7 0x8000800080008001 (rowFbs_27 0) (rowZ_27 0) (rowO_27 0) bit join hgens hfb_16 (zeros_append (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) hz_u_26) (stable_list (stable 0 hk_eq) (rowO_27 0) (by decide +kernel)) cert_27_0
  · have hz_u_26 := uBat hk_eq mi_26 hno_26 (unpackBytes 4 0xf0e0c08) (unpackPerms 4 0x460322004613210046231100463211) (by decide +kernel)
    have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_27 1) (unpackPerms 36 0x3215470032054700310547002105470042153700420537004105370021053700431527004325170043052700432507004105270031052700430517004315070042051700320517004215070032150700521437005204370051043700210437005314270053241700530427005324070051042700310427005304170053140700520417003204170052140700321407) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_27 2) (unpackPerms 30 0x432570004315700043057000421570003215700042057000320570004105700031057000210570005324700054237000543270005314700054137000543170005304700054037000543070005214700054127000542170003214700054207000320470005104700054017000541070003104700021047) (by decide +kernel)
    have hfb_26 := fBat hk_eq mi_26 hno_26 (rowFl_27 3) (unpackPerms 58 0x231547000315470020354700102547001345270003451700420537001025370001452700324517000245170012450700340527004235070012350700204517002135070042051700320517003125070002543700135427000154370003541700254317005214370001243700135407001453070052043700501437005104370001542700351427003542170053142700023417000514270010542700325407003452070014520700530427001234070015240700501427003014270030541700205417003451070053041700203417005134070053140700230417002314070050241700521407) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_27 1) 0 0 0x8000800080008001 (rowFbs_27 1) (rowZ_27 1) [63] bit join hgens (forbs_append (forbs_append hfb_12 hfb_16) hfb_26) (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_26) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_27_1
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_27 4) (unpackPerms 60 0x4325770043157700421577003215770043057700420577003205770041057700310577002105770053247700531477005214770032147700530477005204770032047700510477003104770021047700542377005432770054137700543177005213770042137700540377005430770052037700420377005103770041037700210377005412770054217700531277004312770053217700432177005402770054207700530277004302770053207700432077005102770041027700310277005401770054107700530177004301770053107700431077005201770042017700320177005210770042107700321077) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_27 5) (unpackPerms 20 0x5437700054277000541770005407700053277000432770005317700043177000530770004307700052177000421770003217700052077000420770003207700051077000410770003107700021077) (by decide +kernel)
    have hfb_26 := fBat hk_eq mi_26 hno_26 (rowFl_27 6) ((unpackPerms 64 0x532077004230770043207700123077001502770015207700140277001420770013027700132077005012770051027700401277004102770030127700310277004051770030517700205177004150770031507700215077004501770045107700504177005401770030417700204177005140770054107700314077002140770035017700351077003401770034107700503177005301770040317700430177002031770051307700531077004130770043107700213077002501770025107700240177002410770023017700231077005021770052017700402177004201770030217700320177005120770052107700412077004210770031207700321077) ++ (unpackPerms 64 0x201377002103770041527700315277000152770042517700325177000251770045127700452177005142770054127700314277000142770052417700542177003241770002417700351277003521770034127700342177005132770053127700413277004312770001327700523177005321770042317700432177000231770005127700052177000412770004217700031277000321770040527700305277001052770042507700325077001250770045027700452077005042770054027700304277001042770052407700542077003240770012407700350277003520770034027700342077005032770053027700403277004302770010327700523077) ++ (unpackPerms 64 0x415377002153770001537700435177002351770003517700451377004531770051437700541377002143770001437700534177005431770023417700034177002513770025317700241377002431770051237700521377004123770042137700012377000513770005317700041377000431770002137700405377002053770010537700435077002350770013507700450377004530770050437700540377002043770010437700534077005430770023407700134077002503770025307700240377002430770050237700520377004023770042037700102377001503770015307700140377001430770012037700501377005103770040137700410377) ++ (unpackPerms 64 0x254177002314770051247700521477003124770032147700012477000514770005417700031477000214770030547700205477003450770024507700145077003504770035407700503477005304770020347700103477002504770025407700230477005024770052047700302477003204770010247700150477001540770013047700120477005014770051047700301477003104770020147700210477004253770012537700025377004352770013527700035277004523770045327700524377005423770012437700024377005342770054327700134277000342770015237700153277001423770014327700052377000532770004237700043277) ++ (unpackPerms 64 0x340577004035770043057700203577001035770024057700230577004025770042057700302577003205770010257700140577001305770012057700401577004105770030157700310577002015770021057700235477001354770003547700245377001453770004537700253477002543770015347700154377000534770005437700325477001254770002547700345277001452770004527700352477003542770052347700532477001234770002347700152477001542770013247700052477000542770003247700315477002154770001547700345177002451770004517700351477003541770051347700531477002134770001347700251477) ++ (unpackPerms 38 0x23457700134577000345770024357700143577000435770032457700124577003425770042357700432577001235770002357700142577001325770004257700032577003145770021457700014577003415770041357700431577002135770001357700241577002315770041257700421577003125770032157700012577000415770003157700021577003045770020457700104577)) (by decide +kernel)
    exact cert_step 6 9 hn255 (cFn_27 2) 0 0 0x8000800080008001 (rowFbs_27 2) (rowZ_27 2) [63] bit join hgens (forbs_append (forbs_append hfb_12 hfb_16) hfb_26) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_27_2
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_27 7) (unpackPerms 20 0x54387700542877005328770043287700541877005318770043187700521877004218770032187700540877005308770043087700520877004208770032087700510877004108770031087700210877) (by decide +kernel)
    have hfb_26 := fBat hk_eq mi_26 hno_26 (rowFl_27 8) ((unpackPerms 64 0x314877002148770001487700351877003418770053187700413877004318770021387700013877002518770024187700231877005128770052187700412877004218770031287700321877000128770005187700041877000318770002187700405877003058770020587700105877004508770050487700540877003048770020487700104877003508770034087700503877005308770040387700430877002038770010387700250877002408770023087700502877005208770040287700420877003028770032087700102877001508770014087700130877001208770050187700510877004018770041087700301877003108770020187700210877) ++ (unpackPerms 55 0x345877002458770014587700045877003548770025487700154877000548770043587700235877001358770003587700453877005348770054387700234877001348770003487700253877002438770015387700143877000538770004387700425877003258770012587700025877004528770052487700542877003248770012487700024877003528770034287700523877005328770042387700432877001238770002387700152877001428770013287700052877000428770003287700415877003158770021587700015877004518770051487700541877)) (by decide +kernel)
    exact cert_step 6 8 hn255 (cFn_27 3) 0 0 0x8000800080008001 (rowFbs_27 3) (rowZ_27 3) [63] bit join hgens (forbs_append hfb_12 hfb_26) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_27_3
  · exact cert_step 6 0 hn255 (cFn_27 4) 0 0 0x8000800080008001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_27_4
  · exact cert_step 6 0 hn255 (cFn_27 5) 0 0 0x8000800080008001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_27_5
  · exact cert_step 6 0 hn255 (cFn_27 6) 7 0 0x8000800080008001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_27_6

theorem solve_28 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_12 : ¬ HasCopy 6 mi_12 F)
    (hno_16 : ¬ HasCopy 5 mi_16 F)
    (hno_26 : ¬ HasCopy 6 mi_26 F)
    (hno_27 : ¬ HasCopy 6 mi_27 F)
    (hcopy : HasCopy 5 mi_28 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 5 F closed empty full minSize mi_28 miExp_28 [(15,23)] 0x80808001 wVec_28 fastW_28 1 10 5 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 5) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 5 kv bj F e K sub hk D hD v hv 0x80808001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 5 kv bj F e K sub hk D hD v hv 0x80808001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 5 0 hn255 (cFn_28 0) 0 5 0x80808001 [] (rowZ_28 0) (rowO_28 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_28 0) (by decide +kernel)) cert_28_0
  · have hz_u_26 := uBat hk_eq mi_26 hno_26 (unpackBytes 6 0x1716140f0e0c) (unpackPerms 6 0x3504220035142100352411004503220045132100452311) (by decide +kernel)
    have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_28 0) [0x210435] (by decide +kernel)
    exact cert_step 5 0 hn255 (cFn_28 1) 0 0 0x80808001 (rowFbs_28 1) (rowZ_28 1) [31] bit join hgens hfb_12 (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 16 0x19151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_26) (stable_top (stable 1 hk_eq 31 (Or.inl rfl))) cert_28_1
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_28 1) (unpackPerms 16 0x321466003204660031046600210466004213660042036600410366002103660043126600432166004302660043206600430166004310660042016600320166) (by decide +kernel)
    have hfb_16 := fBat hk_eq mi_16 hno_16 (rowFl_28 2) (unpackPerms 7 0x43266000431660004306600032166000420660003206600041066) (by decide +kernel)
    have hfb_26 := fBat hk_eq mi_26 hno_26 (rowFl_28 3) (unpackPerms 30 0x2134660001346600312466002034660010346600302466003204660031046600124366000243660014326600214366000143660041236600421366002043660010436600402366004203660012036600401366003241660041326600423166003240660040326600103266004230660031406600403166) (by decide +kernel)
    have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_28 4) (unpackPerms 3 0x2143660020436600104366) (by decide +kernel)
    exact cert_step 5 6 hn255 (cFn_28 2) 0 0 0x80808001 (rowFbs_28 2) (rowZ_28 2) [31] bit join hgens (forbs_append (forbs_append (forbs_append hfb_12 hfb_16) hfb_26) hfb_27) (exclude_list (exclude 2 hk_eq) (unpackBytes 6 0x110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 31 (Or.inl rfl))) cert_28_2
  · have hfb_12 := fBat hk_eq mi_12 hno_12 (rowFl_28 5) (unpackPerms 9 0x4327660043176600421766003217660043076600420766003207660041076600310766) (by decide +kernel)
    have hfb_26 := fBat hk_eq mi_26 hno_26 (rowFl_28 6) (unpackPerms 47 0x23476600134766000347660024376600143766003247660012476600024766003427660042376600432766001237660002376600142766001327660004276600032766003147660021476600014766004137660043176600213766000137660023176600421766003217660003176600304766002047660010476600340766004037660043076600203766001037660024076600230766004027660042076600320766001407660013076600401766004107660030176600310766) (by decide +kernel)
    have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_28 7) (unpackPerms 16 0x214766003047660042376600413766002137660040376600203766001037660031276600302766004317660032176600401766003207660041076600210766) (by decide +kernel)
    exact cert_step 5 7 hn255 (cFn_28 3) 0 0 0x80808001 (rowFbs_28 3) (rowZ_28 3) [31] bit join hgens (forbs_append (forbs_append hfb_12 hfb_26) hfb_27) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 31 (Or.inl rfl))) cert_28_3
  · have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_28 8) (unpackPerms 6 0x4387660042876600328766004187660031876600308766) (by decide +kernel)
    exact cert_step 5 3 hn255 (cFn_28 4) 0 0 0x80808001 (rowFbs_28 4) [] [31] bit join hgens hfb_27 (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 31 (Or.inl rfl))) cert_28_4
  · exact cert_step 5 0 hn255 (cFn_28 5) 0 0 0x80808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 31 (Or.inl rfl))) cert_28_5
  · exact cert_step 5 0 hn255 (cFn_28 6) 0 0 0x80808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 31 (Or.inl rfl))) cert_28_6
  · exact cert_step 5 0 hn255 (cFn_28 7) 5 0 0x80808001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 7 hk_eq 31 (Or.inl rfl))) cert_28_7

theorem solve_29 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_27 : ¬ HasCopy 6 mi_27 F)
    (hno_28 : ¬ HasCopy 5 mi_28 F)
    (hcopy : HasCopy 6 mi_29 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_29 miExp_29 [(31,47)] 0x8000800080000001 wVec_29 fastW_29 1 12 0 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 6 kv bj F e K sub hk D hD v hv 0x8000800080000001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 6 0 hn255 (cFn_29 0) 0 0 0x8000800080000001 [] (rowZ_29 0) (rowO_29 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_29 0) (by decide +kernel)) cert_29_0
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_29 0) ((unpackPerms 64 0x10527000415070003051700031507000205170002150700054327000514370005341700054317000214370005043700053407000543070002043700010437000514270005241700054217000314270003241700050427000524070005420700030427000324070001042700050417000514070005410700030417000314070002041700021407000513270005231700053217000413270004231700043217000503270005230700053207000403270004230700043207000103270005031700051307000531070004031700041307000431070002031700021307000502170005120700052107000402170004120700042107000302170003120700032107) ++ (unpackPerms 10 0x21547000205470001054700021537000405370002053700010537000315270003251700030527)) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_29 1) 0 0 0x8000800080000001 (rowFbs_29 1) (rowZ_29 1) [63] bit join hgens hfb_28 (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_29_1
  · have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_29 1) (unpackPerms 40 0x315477002154770030547700215377004053770020537700315277004052770032517700405177004250770032507700415077003150770021507700524377002143770050437700204377001043770031427700504277003241770050417700324077005140770041327700503277005431770042317700503177005230770051307700542177004321770050217700432077005120770043107700521077) (by decide +kernel)
    have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_29 2) (unpackPerms 60 0x435770004257700032577000415770003157700021577000405770003057700020577000105770005347700054377000524770005427700032477000514770005417700031477000214770005047700054077000304770002047700010477000523770005327700042377000432770005137700053177000413770004317700021377000503770005307700040377000430770002037700010377000512770005217700041277000421770003127700032177000502770005207700040277000420770003027700032077000102770005017700051077000401770004107700030177000310770002017700021077) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_29 2) 0 0 0x8000800080000001 (rowFbs_29 2) (rowZ_29 2) [63] bit join hgens (forbs_append hfb_27 hfb_28) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_29_2
  · have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_29 3) (unpackPerms 56 0x43587700425877003258770041587700315877002158770040587700305877002058770010587700534877005248770032487700314877002148770020487700104877005438770052387700423877005138770041387700213877005038770040387700203877001038770054287700432877005128770041287700312877005028770040287700302877001028770054187700531877004318770052187700421877003218770050187700401877003018770020187700540877005308770043087700520877004208770032087700510877004108770031087700210877) (by decide +kernel)
    have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_29 4) (unpackPerms 15 0x548770005387700043877000528770004287700032877000518770004187700031877000218770005087700040877000308770002087700010877) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_29 3) 0 0 0x8000800080000001 (rowFbs_29 3) (rowZ_29 3) [63] bit join hgens (forbs_append hfb_27 hfb_28) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_29_3
  · have hfb_27 := fBat hk_eq mi_27 hno_27 (rowFl_29 5) (unpackPerms 15 0x5498770053987700439877005298770042987700329877005198770041987700319877002198770050987700409877003098770020987700109877) (by decide +kernel)
    exact cert_step 6 4 hn255 (cFn_29 4) 0 0 0x8000800080000001 (rowFbs_29 4) [] [63] bit join hgens hfb_27 (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_29_4
  · exact cert_step 6 0 hn255 (cFn_29 5) 0 0 0x8000800080000001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_29_5
  · exact cert_step 6 0 hn255 (cFn_29 6) 0 0 0x8000800080000001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_29_6

theorem solve_30 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_26 : ¬ HasCopy 6 mi_26 F)
    (hno_28 : ¬ HasCopy 5 mi_28 F)
    (hno_29 : ¬ HasCopy 6 mi_29 F)
    (hcopy : HasCopy 5 mi_30 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 5 F closed empty full minSize mi_30 miExp_30 [] 0x80008001 wVec_30 fastW_30 1 11 6 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 5) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 5 kv bj F e K sub hk D hD v hv 0x80008001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 5 kv bj F e K sub hk D hD v hv 0x80008001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 5 0 hn255 (cFn_30 0) 0 6 0x80008001 [] (rowZ_30 0) (rowO_30 0) bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 25 0x1d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_list (stable 0 hk_eq) (rowO_30 0) (by decide +kernel)) cert_30_0
  · have hz_u_26 := uBat hk_eq mi_26 hno_26 (unpackBytes 4 0xf0e0c08) (unpackPerms 4 0x450322004513210045231100453211) (by decide +kernel)
    have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_30 0) [0x21405] (by decide +kernel)
    exact cert_step 5 0 hn255 (cFn_30 1) 0 0 0x80008001 (rowFbs_30 1) (rowZ_30 1) [31] bit join hgens hfb_28 (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 16 0x19151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_26) (stable_top (stable 1 hk_eq 31 (Or.inl rfl))) cert_30_1
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_30 1) (unpackPerms 25 0x21466000304660004326600041366000431660002136600040366000430660002036600010366000412660004216600031266000321660004026600042066000302660003206600010266000401660004106600030166000310660002016600021066) (by decide +kernel)
    exact cert_step 5 5 hn255 (cFn_30 2) 0 0 0x80008001 (rowFbs_30 2) (rowZ_30 2) [31] bit join hgens hfb_28 (exclude_list (exclude 2 hk_eq) (unpackBytes 6 0x110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 31 (Or.inl rfl))) cert_30_2
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_30 2) (unpackPerms 10 0x43766000427660003276600041766000317660002176600040766000307660002076600010766) (by decide +kernel)
    have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_30 3) (unpackPerms 26 0x32476600314766002147660030476600204766001047660042376600432766004137660043176600213766004037660043076600203766001037660042176600312766004207660032076600102766004017660041076600301766003107660020176600210766) (by decide +kernel)
    exact cert_step 5 6 hn255 (cFn_30 3) 0 0 0x80008001 (rowFbs_30 3) (rowZ_30 3) [31] bit join hgens (forbs_append hfb_28 hfb_29) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 31 (Or.inl rfl))) cert_30_3
  · have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_30 4) (unpackPerms 10 0x438766004287660032876600418766003187660021876600408766003087660020876600108766) (by decide +kernel)
    exact cert_step 5 4 hn255 (cFn_30 4) 0 0 0x80008001 (rowFbs_30 4) [] [31] bit join hgens hfb_29 (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 31 (Or.inl rfl))) cert_30_4
  · exact cert_step 5 0 hn255 (cFn_30 5) 0 0 0x80008001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 31 (Or.inl rfl))) cert_30_5
  · exact cert_step 5 0 hn255 (cFn_30 6) 0 0 0x80008001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 31 (Or.inl rfl))) cert_30_6
  · exact cert_step 5 0 hn255 (cFn_30 7) 6 0 0x80008001 [] [] [31] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 7 hk_eq 31 (Or.inl rfl))) cert_30_7

theorem solve_31 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_28 : ¬ HasCopy 5 mi_28 F)
    (hno_29 : ¬ HasCopy 6 mi_29 F)
    (hno_30 : ¬ HasCopy 5 mi_30 F)
    (hcopy : HasCopy 6 mi_31 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 6 F closed empty full minSize mi_31 miExp_31 [(15,51)] 0x8008000000008001 wVec_31 fastW_31 1 12 6 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 6) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 6 kv bj F e K sub hk D hD v hv 0x8008000000008001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 6 kv bj F e K sub hk D hD v hv 0x8008000000008001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 6 0 hn255 (cFn_31 0) 0 6 0x8008000000008001 [] (rowZ_31 0) [63] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 41 0x39353332312d2b2a29272625242322211d1b1a19171615141312110f0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_top (stable 0 hk_eq 63 (Or.inl rfl))) cert_31_0
  · have hz_u_28 := uBat hk_eq mi_28 hno_28 (unpackBytes 8 0x333224140f0e0c08) (unpackPerms 8 0x654200016541000465110005641100006322000163210002631100036211) (by decide +kernel)
    have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_31 0) [0x10426] (by decide +kernel)
    exact cert_step 6 0 hn255 (cFn_31 1) 0 0 0x8008000000008001 (rowFbs_31 1) (rowZ_31 1) [63] bit join hgens hfb_28 (zeros_append (exclude_list (exclude 1 hk_eq) (unpackBytes 22 0x31292523222119151312110d0b0a0907060504030201) (by decide +kernel)) hz_u_28) (stable_top (stable 1 hk_eq 63 (Or.inl rfl))) cert_31_1
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_31 1) (unpackPerms 53 0x4257700040577000105770005347700054377000524770005427700032477000514770005417700031477000214770005047700054077000304770002047700010477000523770005327700042377000432770005137700053177000413770004317700021377000503770005307700040377000430770002037700010377000512770005217700041277000421770003127700032177000502770005207700040277000420770003027700032077000102770005017700051077000401770004107700030177000310770002017700021077) (by decide +kernel)
    have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_31 2) (unpackPerms 28 0x215477001054770021537700415277004052770010527700415077005142770052417700524077001042770050417700514077002041770021407700532177004321770050327700523077004032770042307700432077005310770040317700502177005120770052107700402177) (by decide +kernel)
    have hfb_30 := fBat hk_eq mi_30 hno_30 (rowFl_31 3) (unpackPerms 39 0x154770000547700045077000243770001437700054277000342770000427700054177000341770002417700004177000540770002407700014077000532770004327700013277000032770005317700043177000231770000317700053077000430770002307700013077000521770004217700032177000021770005207700042077000320770001207700051077000410770003107700021077) (by decide +kernel)
    exact cert_step 6 7 hn255 (cFn_31 2) 0 0 0x8008000000008001 (rowFbs_31 2) (rowZ_31 2) [63] bit join hgens (forbs_append (forbs_append hfb_28 hfb_29) hfb_30) (exclude_list (exclude 2 hk_eq) (unpackBytes 7 0x21110905030201) (by decide +kernel)) (stable_top (stable 2 hk_eq 63 (Or.inl rfl))) cert_31_2
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_31 4) (unpackPerms 14 0x5487700053877000528770004287700032877000518770004187700031877000218770005087700040877000308770002087700010877) (by decide +kernel)
    have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_31 5) (unpackPerms 9 0x5048770010487700521877004218770052087700102877003108770020187700210877) (by decide +kernel)
    have hfb_30 := fBat hk_eq mi_30 hno_30 (rowFl_31 6) (unpackPerms 19 0x34877000148770000487700043877000238770001387700003877000428770003287700012877000028770004187700031877000218770000187700050877000308770002087700010877) (by decide +kernel)
    exact cert_step 6 6 hn255 (cFn_31 3) 0 0 0x8008000000008001 (rowFbs_31 3) (rowZ_31 3) [63] bit join hgens (forbs_append (forbs_append hfb_28 hfb_29) hfb_30) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 63 (Or.inl rfl))) cert_31_3
  · have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_31 7) (unpackPerms 6 0x4398770021987700409877003098770020987700109877) (by decide +kernel)
    have hfb_30 := fBat hk_eq mi_30 hno_30 (rowFl_31 8) (unpackPerms 6 0x598770004987700039877000298770001987700009877) (by decide +kernel)
    exact cert_step 6 4 hn255 (cFn_31 4) 0 0 0x8008000000008001 (rowFbs_31 4) [] [63] bit join hgens (forbs_append hfb_29 hfb_30) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 63 (Or.inl rfl))) cert_31_4
  · exact cert_step 6 0 hn255 (cFn_31 5) 0 0 0x8008000000008001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 63 (Or.inl rfl))) cert_31_5
  · exact cert_step 6 0 hn255 (cFn_31 6) 6 0 0x8008000000008001 [] [] [63] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 63 (Or.inl rfl))) cert_31_6

theorem solve_32 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hno_28 : ¬ HasCopy 5 mi_28 F)
    (hno_29 : ¬ HasCopy 6 mi_29 F)
    (hno_30 : ¬ HasCopy 5 mi_30 F)
    (hno_31 : ¬ HasCopy 6 mi_31 F)
    (hcopy : HasCopy 4 mi_32 F) :
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧ F.card * (∑ i, w i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, w i) := by
  apply solve_row 4 F closed empty full minSize mi_32 miExp_32 [] 0x8001 wVec_32 fastW_32 2 18 16 hcopy (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
  intro e K sub D hD v hv hGenF bit join hgens exclude stable k hk_eq hk_le
  have hn255 : (1 <<< 4) ≤ 255 := by decide
  have uBat {kv bj : ℕ} (hk : K.card = kv) := @unary_batch_list 4 kv bj F e K sub hk D hD v hv 0x8001 hGenF
  have fBat {kv bj : ℕ} (hk : K.card = kv) := @batch_witness_list 4 kv bj F e K sub hk D hD v hv 0x8001 hGenF
  have hk_or : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  rcases hk_or with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_step 4 0 hn255 (cFn_32 0) 0 16 0x8001 [] (rowZ_32 0) [15] bit join hgens (fun _ h => nomatch h) (exclude_list (exclude 0 hk_eq) (unpackBytes 14 0xf0e0d0c0b0a0908070605040302) (by decide +kernel)) (stable_top (stable 0 hk_eq 15 (Or.inl rfl))) cert_32_0
  · have hv_top : 1 ≤ v 15 := stable 1 hk_eq 15 (Or.inl rfl)
    have hdead : v 15 ≤ 0 := by
      simpa using witness_sum_le_fast e K sub hk_eq D hD v hv 0x8001 hGenF mi_30 hno_30 [15] 274960 (by decide +kernel)
    omega
  · have hz_u_31 := uBat hk_eq mi_31 hno_31 (unpackBytes 6 0xd0b0a070604) (unpackPerms 6 0x1054330020543200215431003054220031542100325411) (by decide +kernel)
    exact cert_step 4 0 hn255 (cFn_32 2) 0 0 0x8001 [] (rowZ_32 2) [15] bit join hgens (fun _ h => nomatch h) (zeros_append (exclude_list (exclude 2 hk_eq) (unpackBytes 5 0x905030201) (by decide +kernel)) hz_u_31) (stable_top (stable 2 hk_eq 15 (Or.inl rfl))) cert_32_2
  · have hfb_28 := fBat hk_eq mi_28 hno_28 (rowFl_32 0) (unpackPerms 6 0x326550003165500021655000306550002065500010655) (by decide +kernel)
    have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_32 1) (unpackPerms 3 0x1036550010265500201655) (by decide +kernel)
    have hfb_30 := fBat hk_eq mi_30 hno_30 (rowFl_32 2) (unpackPerms 12 0x236550001365500003655000326550001265500002655000316550002165500001655000306550002065500010655) (by decide +kernel)
    exact cert_step 4 5 hn255 (cFn_32 3) 0 0 0x8001 (rowFbs_32 3) (rowZ_32 3) [15] bit join hgens (forbs_append (forbs_append hfb_28 hfb_29) hfb_30) (exclude_list (exclude 3 hk_eq) [0] (by decide +kernel)) (stable_top (stable 3 hk_eq 15 (Or.inl rfl))) cert_32_3
  · have hfb_29 := fBat hk_eq mi_29 hno_29 (rowFl_32 3) (unpackPerms 2 0x21765500307655) (by decide +kernel)
    have hfb_30 := fBat hk_eq mi_30 hno_30 (rowFl_32 4) (unpackPerms 4 0x37655000276550001765500007655) (by decide +kernel)
    exact cert_step 4 3 hn255 (cFn_32 4) 0 0 0x8001 (rowFbs_32 4) [] [15] bit join hgens (forbs_append hfb_29 hfb_30) (fun _ h => nomatch h) (stable_top (stable 4 hk_eq 15 (Or.inl rfl))) cert_32_4
  · exact cert_step 4 0 hn255 (cFn_32 5) 0 0 0x8001 [] [] [15] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 5 hk_eq 15 (Or.inl rfl))) cert_32_5
  · exact cert_step 4 0 hn255 (cFn_32 6) 0 0 0x8001 [] [] [15] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 6 hk_eq 15 (Or.inl rfl))) cert_32_6
  · exact cert_step 4 0 hn255 (cFn_32 7) 0 0 0x8001 [] [] [15] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 7 hk_eq 15 (Or.inl rfl))) cert_32_7
  · exact cert_step 4 0 hn255 (cFn_32 8) 16 0 0x8001 [] [] [15] bit join hgens (fun _ h => nomatch h) (fun _ h => nomatch h) (stable_top (stable 8 hk_eq 15 (Or.inl rfl))) cert_32_8

end FranklFour

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_univ_card_R2.H2 := by
  intro F closed empty full hex4 minSize
  by_cases h7 : FranklFour.HasCopy 6 FranklFour.mi_7 F
  · exact FranklFour.solve_7 F closed empty full minSize h7
  by_cases h8 : FranklFour.HasCopy 7 FranklFour.mi_8 F
  · exact FranklFour.solve_8 F closed empty full minSize h7 h8
  by_cases h12 : FranklFour.HasCopy 6 FranklFour.mi_12 F
  · exact FranklFour.solve_12 F closed empty full minSize h7 h8 h12
  by_cases h16 : FranklFour.HasCopy 5 FranklFour.mi_16 F
  · exact FranklFour.solve_16 F closed empty full minSize h12 h16
  by_cases h26 : FranklFour.HasCopy 6 FranklFour.mi_26 F
  · exact FranklFour.solve_26 F closed empty full minSize h12 h16 h26
  by_cases h27 : FranklFour.HasCopy 6 FranklFour.mi_27 F
  · exact FranklFour.solve_27 F closed empty full minSize h12 h16 h26 h27
  by_cases h28 : FranklFour.HasCopy 5 FranklFour.mi_28 F
  · exact FranklFour.solve_28 F closed empty full minSize h12 h16 h26 h27 h28
  by_cases h29 : FranklFour.HasCopy 6 FranklFour.mi_29 F
  · exact FranklFour.solve_29 F closed empty full minSize h27 h28 h29
  by_cases h30 : FranklFour.HasCopy 5 FranklFour.mi_30 F
  · exact FranklFour.solve_30 F closed empty full minSize h26 h28 h29 h30
  by_cases h31 : FranklFour.HasCopy 6 FranklFour.mi_31 F
  · exact FranklFour.solve_31 F closed empty full minSize h28 h29 h30 h31
  have h32 : FranklFour.HasCopy 4 FranklFour.mi_32 F := by
    obtain ⟨S, hS, hcard⟩ := hex4
    obtain ⟨e, eqS⟩ := FranklGlobal.coordinates S hcard
    refine ⟨e, ?_⟩
    intro m hm
    have hm15 : m = 15 := by simp only [FranklFour.mi_32, List.mem_singleton] at hm; exact hm
    have hd15 : FranklFour.decode 4 15 = Finset.univ := by decide +kernel
    rw [hm15, hd15, eqS]
    exact hS
  exact FranklFour.solve_32 F closed empty full minSize h28 h29 h30 h31 h32
