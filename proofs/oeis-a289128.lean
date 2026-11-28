import OMAStatements.S_oeis_a289128

-- Problem: A289128: Fixed point of the mapping 00->0010, 01->011, 10->010, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a289128.lean:0 (declaration OMA.S_oeis_a289128.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: decorate each parsed unit (00, 01, 10, 0, 1) with its left and right neighbour
-- unit (with bos/eos at the ends). This closes on 17 tokens (Tok) with carried-in/out
-- single-letter boundaries (ci, Z, co) so step (flat ts) = flat (mu ts) on valid token lists
-- and Valid is preserved by mu via a finite boundary factorisation. Since length is additive
-- and mu is a monoid morphism, every singleton token satisfies the order-5 linear recurrence
-- of A289131 from step 2 onward, giving the recurrence for w(n+7) and matching
-- the 7 initial values.

namespace A289128Proof

open OMA.S_oeis_a289128

inductive Sym
  | bos | eos | u0 | u1 | u00 | u01 | u10
  deriving DecidableEq

def unitS : Sym → List Bool
  | Sym.bos => []
  | Sym.eos => []
  | Sym.u0 => [false]
  | Sym.u1 => [true]
  | Sym.u00 => [false, false]
  | Sym.u01 => [false, true]
  | Sym.u10 => [true, false]

def imgS : Sym → List Bool
  | Sym.bos => []
  | Sym.eos => []
  | Sym.u0 => [false]
  | Sym.u1 => [true]
  | Sym.u00 => [false, false, true, false]
  | Sym.u01 => [false, true, true]
  | Sym.u10 => [false, true, false]

theorem step_unitS : ∀ s : Sym, step (unitS s) = imgS s
  | Sym.bos => rfl
  | Sym.eos => rfl
  | Sym.u0 => rfl
  | Sym.u1 => rfl
  | Sym.u00 => rfl
  | Sym.u01 => rfl
  | Sym.u10 => rfl

inductive Tok
  | t0 -- (00) 1 (10)
  | t1 -- (00) 10 ($)
  | t2 -- (00) 10 (01)
  | t3 -- (01) 0 ($)
  | t4 -- (01) 00 (1)
  | t5 -- (01) 01 (0)
  | t6 -- (01) 01 (00)
  | t7 -- (01) 01 (01)
  | t8 -- (1) 10 ($)
  | t9 -- (1) 10 (01)
  | t10 -- (1) 10 (1)
  | t11 -- (10) 01 (0)
  | t12 -- (10) 01 (00)
  | t13 -- (10) 01 (01)
  | t14 -- (10) 1 (10)
  | t15 -- (^) 00 ($)
  | t16 -- (^) 00 (10)
  deriving DecidableEq

def lft : Tok → Sym
  | Tok.t0 => Sym.u00
  | Tok.t1 => Sym.u00
  | Tok.t2 => Sym.u00
  | Tok.t3 => Sym.u01
  | Tok.t4 => Sym.u01
  | Tok.t5 => Sym.u01
  | Tok.t6 => Sym.u01
  | Tok.t7 => Sym.u01
  | Tok.t8 => Sym.u1
  | Tok.t9 => Sym.u1
  | Tok.t10 => Sym.u1
  | Tok.t11 => Sym.u10
  | Tok.t12 => Sym.u10
  | Tok.t13 => Sym.u10
  | Tok.t14 => Sym.u10
  | Tok.t15 => Sym.bos
  | Tok.t16 => Sym.bos

def mid : Tok → Sym
  | Tok.t0 => Sym.u1
  | Tok.t1 => Sym.u10
  | Tok.t2 => Sym.u10
  | Tok.t3 => Sym.u0
  | Tok.t4 => Sym.u00
  | Tok.t5 => Sym.u01
  | Tok.t6 => Sym.u01
  | Tok.t7 => Sym.u01
  | Tok.t8 => Sym.u10
  | Tok.t9 => Sym.u10
  | Tok.t10 => Sym.u10
  | Tok.t11 => Sym.u01
  | Tok.t12 => Sym.u01
  | Tok.t13 => Sym.u01
  | Tok.t14 => Sym.u1
  | Tok.t15 => Sym.u00
  | Tok.t16 => Sym.u00

def rgt : Tok → Sym
  | Tok.t0 => Sym.u10
  | Tok.t1 => Sym.eos
  | Tok.t2 => Sym.u01
  | Tok.t3 => Sym.eos
  | Tok.t4 => Sym.u1
  | Tok.t5 => Sym.u0
  | Tok.t6 => Sym.u00
  | Tok.t7 => Sym.u01
  | Tok.t8 => Sym.eos
  | Tok.t9 => Sym.u01
  | Tok.t10 => Sym.u1
  | Tok.t11 => Sym.u0
  | Tok.t12 => Sym.u00
  | Tok.t13 => Sym.u01
  | Tok.t14 => Sym.u10
  | Tok.t15 => Sym.eos
  | Tok.t16 => Sym.u10

def ci : Tok → List Bool
  | Tok.t0 => [false]
  | Tok.t1 => []
  | Tok.t2 => []
  | Tok.t3 => [true]
  | Tok.t4 => [true]
  | Tok.t5 => [true]
  | Tok.t6 => [true]
  | Tok.t7 => [true]
  | Tok.t8 => []
  | Tok.t9 => []
  | Tok.t10 => []
  | Tok.t11 => [false]
  | Tok.t12 => [false]
  | Tok.t13 => [false]
  | Tok.t14 => [false]
  | Tok.t15 => []
  | Tok.t16 => []

def Z : Tok → List Bool
  | Tok.t0 => [true]
  | Tok.t1 => [false, true, false]
  | Tok.t2 => [false, true]
  | Tok.t3 => [false]
  | Tok.t4 => [false, false, true]
  | Tok.t5 => [false, true]
  | Tok.t6 => [false, true]
  | Tok.t7 => [false, true]
  | Tok.t8 => [false, true, false]
  | Tok.t9 => [false, true]
  | Tok.t10 => [false, true]
  | Tok.t11 => [false, true]
  | Tok.t12 => [false, true]
  | Tok.t13 => [false, true]
  | Tok.t14 => [true]
  | Tok.t15 => [false, false, true, false]
  | Tok.t16 => [false, false, true, false]

def co : Tok → List Bool
  | Tok.t0 => []
  | Tok.t1 => []
  | Tok.t2 => [false]
  | Tok.t3 => []
  | Tok.t4 => [false]
  | Tok.t5 => [true]
  | Tok.t6 => [true]
  | Tok.t7 => [true]
  | Tok.t8 => []
  | Tok.t9 => [false]
  | Tok.t10 => [false]
  | Tok.t11 => [true]
  | Tok.t12 => [true]
  | Tok.t13 => [true]
  | Tok.t14 => []
  | Tok.t15 => []
  | Tok.t16 => []

def headM : Tok → Tok
  | Tok.t0 => Tok.t7
  | Tok.t1 => Tok.t11
  | Tok.t2 => Tok.t12
  | Tok.t3 => Tok.t8
  | Tok.t4 => Tok.t9
  | Tok.t5 => Tok.t10
  | Tok.t6 => Tok.t10
  | Tok.t7 => Tok.t10
  | Tok.t8 => Tok.t5
  | Tok.t9 => Tok.t6
  | Tok.t10 => Tok.t7
  | Tok.t11 => Tok.t4
  | Tok.t12 => Tok.t4
  | Tok.t13 => Tok.t4
  | Tok.t14 => Tok.t7
  | Tok.t15 => Tok.t16
  | Tok.t16 => Tok.t16

def tailM : Tok → List Tok
  | Tok.t0 => []
  | Tok.t1 => [Tok.t3]
  | Tok.t2 => []
  | Tok.t3 => []
  | Tok.t4 => [Tok.t13]
  | Tok.t5 => [Tok.t14]
  | Tok.t6 => [Tok.t14]
  | Tok.t7 => [Tok.t14]
  | Tok.t8 => [Tok.t3]
  | Tok.t9 => []
  | Tok.t10 => []
  | Tok.t11 => [Tok.t0]
  | Tok.t12 => [Tok.t0]
  | Tok.t13 => [Tok.t0]
  | Tok.t14 => []
  | Tok.t15 => [Tok.t1]
  | Tok.t16 => [Tok.t2]

def lastM : Tok → Tok
  | Tok.t0 => Tok.t7
  | Tok.t1 => Tok.t3
  | Tok.t2 => Tok.t12
  | Tok.t3 => Tok.t8
  | Tok.t4 => Tok.t13
  | Tok.t5 => Tok.t14
  | Tok.t6 => Tok.t14
  | Tok.t7 => Tok.t14
  | Tok.t8 => Tok.t3
  | Tok.t9 => Tok.t6
  | Tok.t10 => Tok.t7
  | Tok.t11 => Tok.t0
  | Tok.t12 => Tok.t0
  | Tok.t13 => Tok.t0
  | Tok.t14 => Tok.t7
  | Tok.t15 => Tok.t1
  | Tok.t16 => Tok.t2

def mu1 (t : Tok) : List Tok := headM t :: tailM t

def flat : List Tok → List Bool
  | [] => []
  | t :: ts => unitS (mid t) ++ flat ts

def mu : List Tok → List Tok
  | [] => []
  | t :: ts => mu1 t ++ mu ts

theorem flat_append : ∀ a b : List Tok, flat (a ++ b) = flat a ++ flat b
  | [], _ => rfl
  | t :: a, b => by
    show unitS (mid t) ++ flat (a ++ b) = (unitS (mid t) ++ flat a) ++ flat b
    rw [flat_append a b, List.append_assoc]

theorem tok_img (t : Tok) : imgS (mid t) = Z t ++ co t := by
  cases t <;> rfl

theorem tok_flat (t : Tok) : ci t ++ Z t = flat (mu1 t) := by
  cases t <;> rfl

theorem mid_ne_bos (t : Tok) : mid t ≠ Sym.bos := by
  cases t <;> decide

theorem mid_ne_eos (t : Tok) : mid t ≠ Sym.eos := by
  cases t <;> decide

theorem u0_rgt_eos (t : Tok) : mid t = Sym.u0 → rgt t = Sym.eos := by
  cases t <;> decide

theorem u1_rgt_ok (t : Tok) : mid t = Sym.u1 → rgt t = Sym.u1 ∨ rgt t = Sym.u10 ∨ rgt t = Sym.eos := by
  cases t <;> decide

theorem step_unit_adj (a b : Tok) (r : List Bool) (h : rgt a = mid b) :
    step (unitS (mid a) ++ (unitS (mid b) ++ r)) = imgS (mid a) ++ step (unitS (mid b) ++ r) := by
  cases hm : mid a with
  | bos => exact False.elim (mid_ne_bos a hm)
  | eos => exact False.elim (mid_ne_eos a hm)
  | u0 =>
    have h1 : rgt a = Sym.eos := u0_rgt_eos a hm
    rw [h] at h1
    exact False.elim (mid_ne_eos b h1)
  | u00 => rfl
  | u01 => rfl
  | u10 => rfl
  | u1 =>
    have h1 := u1_rgt_ok a hm
    rw [h] at h1
    rcases h1 with hb | hb | hb
    · rw [hb]; rfl
    · rw [hb]; rfl
    · exact False.elim (mid_ne_eos b hb)

def adj (a b : Tok) : Prop :=
  rgt a = mid b ∧ lft b = mid a ∧ co a = ci b

def ChainEnd : Tok → List Tok → Prop
  | a, [] => rgt a = Sym.eos ∧ co a = []
  | a, b :: ts => adj a b ∧ ChainEnd b ts

def ChainTo : Tok → List Tok → Tok → Prop
  | a, [], last => a = last
  | a, b :: xs, last => adj a b ∧ ChainTo b xs last

def Valid : List Tok → Prop
  | [] => False
  | t :: ts => lft t = Sym.bos ∧ ci t = [] ∧ ChainEnd t ts

theorem step_chain : ∀ (a : Tok) (ts : List Tok),
    ChainEnd a ts → ci a ++ step (unitS (mid a) ++ flat ts) = flat (mu (a :: ts))
  | a, [], h => by
    show ci a ++ step (unitS (mid a) ++ []) = flat (mu1 a ++ [])
    rw [List.append_nil, List.append_nil, step_unitS, tok_img a, h.2, List.append_nil, tok_flat a]
  | a, b :: ts, ⟨hab, hrest⟩ => by
    have ih := step_chain b ts hrest
    show ci a ++ step (unitS (mid a) ++ (unitS (mid b) ++ flat ts)) = flat (mu1 a ++ mu (b :: ts))
    rw [step_unit_adj a b (flat ts) hab.1, tok_img a, flat_append, ← tok_flat a]
    rw [List.append_assoc, List.append_assoc, hab.2.2, ih]

theorem step_valid : ∀ ts : List Tok, Valid ts → step (flat ts) = flat (mu ts)
  | [], h => False.elim h
  | t :: ts, ⟨_, hci, hce⟩ => by
    have h := step_chain t ts hce
    rw [hci, List.nil_append] at h
    exact h

def fL : Sym → Sym → List Bool → Sym
  | Sym.u00, Sym.u1, [false] => Sym.u01
  | Sym.u00, Sym.u10, [] => Sym.u10
  | Sym.u01, Sym.u0, [true] => Sym.u1
  | Sym.u01, Sym.u00, [true] => Sym.u1
  | Sym.u01, Sym.u01, [true] => Sym.u1
  | Sym.u1, Sym.u10, [] => Sym.u01
  | Sym.u10, Sym.u01, [false] => Sym.u01
  | Sym.u10, Sym.u1, [false] => Sym.u01
  | _, _, _ => Sym.bos

def fR : Sym → Sym → List Bool → Sym
  | Sym.u00, Sym.u1, [false] => Sym.u01
  | Sym.u00, Sym.u10, [] => Sym.u01
  | Sym.u01, Sym.u0, [true] => Sym.u10
  | Sym.u01, Sym.u00, [true] => Sym.u10
  | Sym.u01, Sym.u01, [true] => Sym.u10
  | Sym.u1, Sym.u10, [] => Sym.u01
  | Sym.u10, Sym.u01, [false] => Sym.u00
  | Sym.u10, Sym.u1, [false] => Sym.u01
  | _, _, _ => Sym.bos

def fC : Sym → Sym → List Bool → List Bool
  | Sym.u00, Sym.u1, [false] => [true]
  | Sym.u00, Sym.u10, [] => [false]
  | Sym.u01, Sym.u0, [true] => []
  | Sym.u01, Sym.u00, [true] => []
  | Sym.u01, Sym.u01, [true] => []
  | Sym.u1, Sym.u10, [] => [true]
  | Sym.u10, Sym.u01, [false] => [true]
  | Sym.u10, Sym.u1, [false] => [true]
  | _, _, _ => []

theorem last_bL (t : Tok) : rgt t ≠ Sym.eos → mid (lastM t) = fL (mid t) (rgt t) (co t) := by
  cases t <;> decide

theorem last_bR (t : Tok) : rgt t ≠ Sym.eos → rgt (lastM t) = fR (mid t) (rgt t) (co t) := by
  cases t <;> decide

theorem last_bC (t : Tok) : rgt t ≠ Sym.eos → co (lastM t) = fC (mid t) (rgt t) (co t) := by
  cases t <;> decide

theorem head_bL (t : Tok) : lft t ≠ Sym.bos → lft (headM t) = fL (lft t) (mid t) (ci t) := by
  cases t <;> decide

theorem head_bR (t : Tok) : lft t ≠ Sym.bos → mid (headM t) = fR (lft t) (mid t) (ci t) := by
  cases t <;> decide

theorem head_bC (t : Tok) : lft t ≠ Sym.bos → ci (headM t) = fC (lft t) (mid t) (ci t) := by
  cases t <;> decide

theorem adj_mu (a b : Tok) (h : adj a b) : adj (lastM a) (headM b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have ha : rgt a ≠ Sym.eos := by rw [h1]; exact mid_ne_eos b
  have hb : lft b ≠ Sym.bos := by rw [h2]; exact mid_ne_bos a
  refine ⟨?_, ?_, ?_⟩
  · rw [last_bR a ha, head_bR b hb, h1, h2, h3]
  · rw [head_bL b hb, last_bL a ha, h1, h2, h3]
  · rw [last_bC a ha, head_bC b hb, h1, h2, h3]

theorem start_mu (t : Tok) : lft t = Sym.bos → lft (headM t) = Sym.bos ∧ ci (headM t) = [] := by
  cases t <;> decide

theorem end_mu (t : Tok) : rgt t = Sym.eos → rgt (lastM t) = Sym.eos ∧ co (lastM t) = [] := by
  cases t <;> decide

theorem mu1_chain (t : Tok) : ChainTo (headM t) (tailM t) (lastM t) := by
  cases t with
  | t0 => exact rfl
  | t1 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t2 => exact rfl
  | t3 => exact rfl
  | t4 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t5 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t6 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t7 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t8 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t9 => exact rfl
  | t10 => exact rfl
  | t11 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t12 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t13 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t14 => exact rfl
  | t15 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t16 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

theorem chainTo_end : ∀ (a last : Tok) (xs : List Tok),
    ChainTo a xs last → (rgt last = Sym.eos ∧ co last = []) → ChainEnd a xs
  | _, _, [], rfl, hend => hend
  | _, last, c :: xs, ⟨hac, hrest⟩, hend => ⟨hac, chainTo_end c last xs hrest hend⟩

theorem chainTo_append_end : ∀ (a last b : Tok) (xs ys : List Tok),
    ChainTo a xs last → adj last b → ChainEnd b ys → ChainEnd a (xs ++ b :: ys)
  | _, _, _, [], _, rfl, hab, hys => ⟨hab, hys⟩
  | _, last, b, c :: xs, ys, ⟨hac, hrest⟩, hab, hys =>
    ⟨hac, chainTo_append_end c last b xs ys hrest hab hys⟩

theorem chainEnd_mu : ∀ (a : Tok) (ts : List Tok),
    ChainEnd a ts → ChainEnd (headM a) (tailM a ++ mu ts)
  | a, [], h => by
    show ChainEnd (headM a) (tailM a ++ [])
    rw [List.append_nil]
    exact chainTo_end (headM a) (lastM a) (tailM a) (mu1_chain a) (end_mu a h.1)
  | a, b :: ts, ⟨hab, hrest⟩ => by
    have ih := chainEnd_mu b ts hrest
    show ChainEnd (headM a) (tailM a ++ (headM b :: tailM b ++ mu ts))
    rw [List.cons_append]
    exact chainTo_append_end (headM a) (lastM a) (headM b) (tailM a) (tailM b ++ mu ts)
      (mu1_chain a) (adj_mu a b hab) ih

theorem valid_mu : ∀ ts : List Tok, Valid ts → Valid (mu ts)
  | [], h => False.elim h
  | t :: ts, ⟨hl, _, hce⟩ => by
    show Valid (headM t :: tailM t ++ mu ts)
    rw [List.cons_append]
    have hs := start_mu t hl
    exact ⟨hs.1, hs.2, chainEnd_mu t ts hce⟩

def toks : ℕ → List Tok
  | 0 => [Tok.t15]
  | n + 1 => mu (toks n)

theorem toks_valid : ∀ n : ℕ, Valid (toks n)
  | 0 => ⟨rfl, rfl, ⟨rfl, rfl⟩⟩
  | n + 1 => valid_mu (toks n) (toks_valid n)

theorem w_eq_flat : ∀ n : ℕ, w n = flat (toks n)
  | 0 => rfl
  | n + 1 => by
    show step (w n) = flat (mu (toks n))
    rw [w_eq_flat n, step_valid (toks n) (toks_valid n)]

def listSum (f : Tok → ℤ) : List Tok → ℤ
  | [] => 0
  | t :: ts => f t + listSum f ts

theorem listSum_append (f : Tok → ℤ) : ∀ a b : List Tok,
    listSum f (a ++ b) = listSum f a + listSum f b
  | [], b => by
    show listSum f b = 0 + listSum f b
    ring
  | t :: a, b => by
    show f t + listSum f (a ++ b) = f t + listSum f a + listSum f b
    rw [listSum_append f a b]
    ring

def wLen : ℕ → Tok → ℤ
  | 0, t => ((unitS (mid t)).length : ℤ)
  | k + 1, t => listSum (wLen k) (mu1 t)

theorem len_flat : ∀ ts : List Tok, ((flat ts).length : ℤ) = listSum (wLen 0) ts
  | [] => rfl
  | t :: ts => by
    show (((unitS (mid t) ++ flat ts).length : ℕ) : ℤ) = ((unitS (mid t)).length : ℤ) + listSum (wLen 0) ts
    rw [List.length_append, Nat.cast_add, len_flat ts]

theorem listSum_mu (k : ℕ) : ∀ ts : List Tok, listSum (wLen k) (mu ts) = listSum (wLen (k + 1)) ts
  | [] => rfl
  | t :: ts => by
    show listSum (wLen k) (mu1 t ++ mu ts) = listSum (wLen k) (mu1 t) + listSum (wLen (k + 1)) ts
    rw [listSum_append, listSum_mu k ts]

theorem len_w_add : ∀ (k n : ℕ), ((w (n + k)).length : ℤ) = listSum (wLen k) (toks n)
  | 0, n => by
    rw [Nat.add_zero, w_eq_flat n, len_flat]
  | k + 1, n => by
    have ih := len_w_add k (n + 1)
    rw [show n + 1 + k = n + (k + 1) by omega] at ih
    rw [ih]
    show listSum (wLen k) (mu (toks n)) = listSum (wLen (k + 1)) (toks n)
    exact listSum_mu k (toks n)

theorem wLen_rec (t : Tok) : wLen 7 t = wLen 6 t + 3 * wLen 5 t - 3 * wLen 4 t - 2 * wLen 3 t + 2 * wLen 2 t := by
  cases t <;> decide

theorem listSum_rec : ∀ ts : List Tok, listSum (wLen 7) ts = listSum (wLen 6) ts + 3 * listSum (wLen 5) ts - 3 * listSum (wLen 4) ts - 2 * listSum (wLen 3) ts + 2 * listSum (wLen 2) ts
  | [] => rfl
  | t :: ts => by
    have ht := wLen_rec t
    have ih := listSum_rec ts
    simp only [listSum]
    linear_combination ht + ih

theorem len_rec (n : ℕ) : ((w (n + 7)).length : ℤ) = ((w (n + 6)).length : ℤ) + 3 * ((w (n + 5)).length : ℤ) - 3 * ((w (n + 4)).length : ℤ) - 2 * ((w (n + 3)).length : ℤ) + 2 * ((w (n + 2)).length : ℤ) := by
  rw [len_w_add 2 n]
  rw [len_w_add 3 n]
  rw [len_w_add 4 n]
  rw [len_w_add 5 n]
  rw [len_w_add 6 n]
  rw [len_w_add 7 n]
  exact listSum_rec (toks n)

theorem base_eq (k : ℕ) (hk : k < 7) : ((w k).length : ℤ) = A289131 k := by
  have h0 : ((w (0 + k)).length : ℤ) = listSum (wLen k) (toks 0) := len_w_add k 0
  rw [Nat.zero_add] at h0
  rw [h0]
  interval_cases k <;> decide

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A289131 n ∧
    ((w (n + 1)).length : ℤ) = A289131 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A289131 (n + 2) ∧
    ((w (n + 3)).length : ℤ) = A289131 (n + 3) ∧
    ((w (n + 4)).length : ℤ) = A289131 (n + 4) ∧
    ((w (n + 5)).length : ℤ) = A289131 (n + 5) ∧
    ((w (n + 6)).length : ℤ) = A289131 (n + 6)
  | 0 => ⟨base_eq 0 (by omega), base_eq 1 (by omega), base_eq 2 (by omega), base_eq 3 (by omega), base_eq 4 (by omega), base_eq 5 (by omega), base_eq 6 (by omega)⟩
  | n + 1 => by
    obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    show ((w (n + 7)).length : ℤ) = A289131 (n + 7)
    have hA : A289131 (n + 7) = A289131 (n + 6) + 3 * A289131 (n + 5) - 3 * A289131 (n + 4) - 2 * A289131 (n + 3) + 2 * A289131 (n + 2) := rfl
    rw [hA, ← h6, ← h5, ← h4, ← h3, ← h2]
    exact len_rec n

end A289128Proof

open OMA.S_oeis_a289128 A289128Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a289128.main := by
  intro n
  exact (len_eq n).1
