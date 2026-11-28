import OMAStatements.S_oeis_a289104

-- Problem: A289104: Fixed point of the mapping 00->0010, 01->011, 10->000, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a289104.lean:0 (declaration OMA.S_oeis_a289104.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: decorate each parsed unit (00, 01, 10, 0, 1) with its left and right neighbour
-- unit (with bos/eos at the ends). This closes on 26 tokens (Tok) with carried-in/out
-- single-letter boundaries (ci, Z, co) so step (flat ts) = flat (mu ts) on valid token lists
-- and Valid is preserved by mu via a finite boundary factorisation. Since length is additive
-- and mu is a monoid morphism, every singleton token satisfies the order-3 linear recurrence
-- of A289107 from step 4 onward, giving the recurrence for w(n+7) and matching
-- the 7 initial values.

namespace A289104Proof

open OMA.S_oeis_a289104

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
  | Sym.u10 => [false, false, false]

theorem step_unitS : ∀ s : Sym, step (unitS s) = imgS s
  | Sym.bos => rfl
  | Sym.eos => rfl
  | Sym.u0 => rfl
  | Sym.u1 => rfl
  | Sym.u00 => rfl
  | Sym.u01 => rfl
  | Sym.u10 => rfl

inductive Tok
  | t0 -- (00) 0 ($)
  | t1 -- (00) 00 (01)
  | t2 -- (00) 00 (1)
  | t3 -- (00) 01 (00)
  | t4 -- (00) 01 (01)
  | t5 -- (00) 1 (10)
  | t6 -- (00) 10 ($)
  | t7 -- (00) 10 (00)
  | t8 -- (01) 0 ($)
  | t9 -- (01) 00 ($)
  | t10 -- (01) 00 (0)
  | t11 -- (01) 00 (00)
  | t12 -- (01) 00 (01)
  | t13 -- (01) 00 (1)
  | t14 -- (01) 01 (00)
  | t15 -- (1) 10 ($)
  | t16 -- (1) 10 (01)
  | t17 -- (1) 10 (1)
  | t18 -- (10) 00 (0)
  | t19 -- (10) 00 (00)
  | t20 -- (10) 01 (0)
  | t21 -- (10) 01 (00)
  | t22 -- (10) 01 (01)
  | t23 -- (10) 1 (10)
  | t24 -- (^) 00 ($)
  | t25 -- (^) 00 (10)
  deriving DecidableEq

def lft : Tok → Sym
  | Tok.t0 => Sym.u00
  | Tok.t1 => Sym.u00
  | Tok.t2 => Sym.u00
  | Tok.t3 => Sym.u00
  | Tok.t4 => Sym.u00
  | Tok.t5 => Sym.u00
  | Tok.t6 => Sym.u00
  | Tok.t7 => Sym.u00
  | Tok.t8 => Sym.u01
  | Tok.t9 => Sym.u01
  | Tok.t10 => Sym.u01
  | Tok.t11 => Sym.u01
  | Tok.t12 => Sym.u01
  | Tok.t13 => Sym.u01
  | Tok.t14 => Sym.u01
  | Tok.t15 => Sym.u1
  | Tok.t16 => Sym.u1
  | Tok.t17 => Sym.u1
  | Tok.t18 => Sym.u10
  | Tok.t19 => Sym.u10
  | Tok.t20 => Sym.u10
  | Tok.t21 => Sym.u10
  | Tok.t22 => Sym.u10
  | Tok.t23 => Sym.u10
  | Tok.t24 => Sym.bos
  | Tok.t25 => Sym.bos

def mid : Tok → Sym
  | Tok.t0 => Sym.u0
  | Tok.t1 => Sym.u00
  | Tok.t2 => Sym.u00
  | Tok.t3 => Sym.u01
  | Tok.t4 => Sym.u01
  | Tok.t5 => Sym.u1
  | Tok.t6 => Sym.u10
  | Tok.t7 => Sym.u10
  | Tok.t8 => Sym.u0
  | Tok.t9 => Sym.u00
  | Tok.t10 => Sym.u00
  | Tok.t11 => Sym.u00
  | Tok.t12 => Sym.u00
  | Tok.t13 => Sym.u00
  | Tok.t14 => Sym.u01
  | Tok.t15 => Sym.u10
  | Tok.t16 => Sym.u10
  | Tok.t17 => Sym.u10
  | Tok.t18 => Sym.u00
  | Tok.t19 => Sym.u00
  | Tok.t20 => Sym.u01
  | Tok.t21 => Sym.u01
  | Tok.t22 => Sym.u01
  | Tok.t23 => Sym.u1
  | Tok.t24 => Sym.u00
  | Tok.t25 => Sym.u00

def rgt : Tok → Sym
  | Tok.t0 => Sym.eos
  | Tok.t1 => Sym.u01
  | Tok.t2 => Sym.u1
  | Tok.t3 => Sym.u00
  | Tok.t4 => Sym.u01
  | Tok.t5 => Sym.u10
  | Tok.t6 => Sym.eos
  | Tok.t7 => Sym.u00
  | Tok.t8 => Sym.eos
  | Tok.t9 => Sym.eos
  | Tok.t10 => Sym.u0
  | Tok.t11 => Sym.u00
  | Tok.t12 => Sym.u01
  | Tok.t13 => Sym.u1
  | Tok.t14 => Sym.u00
  | Tok.t15 => Sym.eos
  | Tok.t16 => Sym.u01
  | Tok.t17 => Sym.u1
  | Tok.t18 => Sym.u0
  | Tok.t19 => Sym.u00
  | Tok.t20 => Sym.u0
  | Tok.t21 => Sym.u00
  | Tok.t22 => Sym.u01
  | Tok.t23 => Sym.u10
  | Tok.t24 => Sym.eos
  | Tok.t25 => Sym.u10

def ci : Tok → List Bool
  | Tok.t0 => [false]
  | Tok.t1 => [false]
  | Tok.t2 => [false]
  | Tok.t3 => [false]
  | Tok.t4 => [false]
  | Tok.t5 => [false]
  | Tok.t6 => []
  | Tok.t7 => []
  | Tok.t8 => [true]
  | Tok.t9 => [true]
  | Tok.t10 => [true]
  | Tok.t11 => [true]
  | Tok.t12 => [true]
  | Tok.t13 => [true]
  | Tok.t14 => [true]
  | Tok.t15 => []
  | Tok.t16 => []
  | Tok.t17 => []
  | Tok.t18 => [false]
  | Tok.t19 => [false]
  | Tok.t20 => [false]
  | Tok.t21 => [false]
  | Tok.t22 => [false]
  | Tok.t23 => [false]
  | Tok.t24 => []
  | Tok.t25 => []

def Z : Tok → List Bool
  | Tok.t0 => [false]
  | Tok.t1 => [false, false, true]
  | Tok.t2 => [false, false, true]
  | Tok.t3 => [false, true]
  | Tok.t4 => [false, true]
  | Tok.t5 => [true]
  | Tok.t6 => [false, false, false]
  | Tok.t7 => [false, false]
  | Tok.t8 => [false]
  | Tok.t9 => [false, false, true, false]
  | Tok.t10 => [false, false, true]
  | Tok.t11 => [false, false, true]
  | Tok.t12 => [false, false, true]
  | Tok.t13 => [false, false, true]
  | Tok.t14 => [false, true]
  | Tok.t15 => [false, false, false]
  | Tok.t16 => [false, false]
  | Tok.t17 => [false, false]
  | Tok.t18 => [false, false, true]
  | Tok.t19 => [false, false, true]
  | Tok.t20 => [false, true]
  | Tok.t21 => [false, true]
  | Tok.t22 => [false, true]
  | Tok.t23 => [true]
  | Tok.t24 => [false, false, true, false]
  | Tok.t25 => [false, false, true, false]

def co : Tok → List Bool
  | Tok.t0 => []
  | Tok.t1 => [false]
  | Tok.t2 => [false]
  | Tok.t3 => [true]
  | Tok.t4 => [true]
  | Tok.t5 => []
  | Tok.t6 => []
  | Tok.t7 => [false]
  | Tok.t8 => []
  | Tok.t9 => []
  | Tok.t10 => [false]
  | Tok.t11 => [false]
  | Tok.t12 => [false]
  | Tok.t13 => [false]
  | Tok.t14 => [true]
  | Tok.t15 => []
  | Tok.t16 => [false]
  | Tok.t17 => [false]
  | Tok.t18 => [false]
  | Tok.t19 => [false]
  | Tok.t20 => [true]
  | Tok.t21 => [true]
  | Tok.t22 => [true]
  | Tok.t23 => []
  | Tok.t24 => []
  | Tok.t25 => []

def headM : Tok → Tok
  | Tok.t0 => Tok.t9
  | Tok.t1 => Tok.t12
  | Tok.t2 => Tok.t12
  | Tok.t3 => Tok.t13
  | Tok.t4 => Tok.t13
  | Tok.t5 => Tok.t14
  | Tok.t6 => Tok.t18
  | Tok.t7 => Tok.t19
  | Tok.t8 => Tok.t15
  | Tok.t9 => Tok.t16
  | Tok.t10 => Tok.t16
  | Tok.t11 => Tok.t16
  | Tok.t12 => Tok.t16
  | Tok.t13 => Tok.t16
  | Tok.t14 => Tok.t17
  | Tok.t15 => Tok.t10
  | Tok.t16 => Tok.t11
  | Tok.t17 => Tok.t12
  | Tok.t18 => Tok.t1
  | Tok.t19 => Tok.t1
  | Tok.t20 => Tok.t2
  | Tok.t21 => Tok.t2
  | Tok.t22 => Tok.t2
  | Tok.t23 => Tok.t3
  | Tok.t24 => Tok.t25
  | Tok.t25 => Tok.t25

def tailM : Tok → List Tok
  | Tok.t0 => []
  | Tok.t1 => [Tok.t3]
  | Tok.t2 => [Tok.t4]
  | Tok.t3 => [Tok.t5]
  | Tok.t4 => [Tok.t5]
  | Tok.t5 => []
  | Tok.t6 => [Tok.t0]
  | Tok.t7 => []
  | Tok.t8 => []
  | Tok.t9 => [Tok.t20, Tok.t8]
  | Tok.t10 => [Tok.t21]
  | Tok.t11 => [Tok.t21]
  | Tok.t12 => [Tok.t21]
  | Tok.t13 => [Tok.t22]
  | Tok.t14 => [Tok.t23]
  | Tok.t15 => [Tok.t0]
  | Tok.t16 => []
  | Tok.t17 => []
  | Tok.t18 => [Tok.t3]
  | Tok.t19 => [Tok.t3]
  | Tok.t20 => [Tok.t5]
  | Tok.t21 => [Tok.t5]
  | Tok.t22 => [Tok.t5]
  | Tok.t23 => []
  | Tok.t24 => [Tok.t6]
  | Tok.t25 => [Tok.t7]

def lastM : Tok → Tok
  | Tok.t0 => Tok.t9
  | Tok.t1 => Tok.t3
  | Tok.t2 => Tok.t4
  | Tok.t3 => Tok.t5
  | Tok.t4 => Tok.t5
  | Tok.t5 => Tok.t14
  | Tok.t6 => Tok.t0
  | Tok.t7 => Tok.t19
  | Tok.t8 => Tok.t15
  | Tok.t9 => Tok.t8
  | Tok.t10 => Tok.t21
  | Tok.t11 => Tok.t21
  | Tok.t12 => Tok.t21
  | Tok.t13 => Tok.t22
  | Tok.t14 => Tok.t23
  | Tok.t15 => Tok.t0
  | Tok.t16 => Tok.t11
  | Tok.t17 => Tok.t12
  | Tok.t18 => Tok.t3
  | Tok.t19 => Tok.t3
  | Tok.t20 => Tok.t5
  | Tok.t21 => Tok.t5
  | Tok.t22 => Tok.t5
  | Tok.t23 => Tok.t3
  | Tok.t24 => Tok.t6
  | Tok.t25 => Tok.t7

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
  | Sym.u00, Sym.u0, [false] => Sym.u01
  | Sym.u00, Sym.u00, [false] => Sym.u01
  | Sym.u00, Sym.u01, [false] => Sym.u01
  | Sym.u00, Sym.u1, [false] => Sym.u01
  | Sym.u00, Sym.u10, [] => Sym.u10
  | Sym.u01, Sym.u0, [true] => Sym.u1
  | Sym.u01, Sym.u00, [true] => Sym.u1
  | Sym.u01, Sym.u01, [true] => Sym.u1
  | Sym.u1, Sym.u10, [] => Sym.u01
  | Sym.u10, Sym.u00, [false] => Sym.u00
  | Sym.u10, Sym.u01, [false] => Sym.u00
  | Sym.u10, Sym.u1, [false] => Sym.u00
  | _, _, _ => Sym.bos

def fR : Sym → Sym → List Bool → Sym
  | Sym.u00, Sym.u0, [false] => Sym.u00
  | Sym.u00, Sym.u00, [false] => Sym.u00
  | Sym.u00, Sym.u01, [false] => Sym.u00
  | Sym.u00, Sym.u1, [false] => Sym.u01
  | Sym.u00, Sym.u10, [] => Sym.u00
  | Sym.u01, Sym.u0, [true] => Sym.u10
  | Sym.u01, Sym.u00, [true] => Sym.u10
  | Sym.u01, Sym.u01, [true] => Sym.u10
  | Sym.u1, Sym.u10, [] => Sym.u00
  | Sym.u10, Sym.u00, [false] => Sym.u00
  | Sym.u10, Sym.u01, [false] => Sym.u00
  | Sym.u10, Sym.u1, [false] => Sym.u01
  | _, _, _ => Sym.bos

def fC : Sym → Sym → List Bool → List Bool
  | Sym.u00, Sym.u0, [false] => [true]
  | Sym.u00, Sym.u00, [false] => [true]
  | Sym.u00, Sym.u01, [false] => [true]
  | Sym.u00, Sym.u1, [false] => [true]
  | Sym.u00, Sym.u10, [] => [false]
  | Sym.u01, Sym.u0, [true] => []
  | Sym.u01, Sym.u00, [true] => []
  | Sym.u01, Sym.u01, [true] => []
  | Sym.u1, Sym.u10, [] => [true]
  | Sym.u10, Sym.u00, [false] => [false]
  | Sym.u10, Sym.u01, [false] => [false]
  | Sym.u10, Sym.u1, [false] => [false]
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
  | t2 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t3 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t4 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t5 => exact rfl
  | t6 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t7 => exact rfl
  | t8 => exact rfl
  | t9 => exact ⟨⟨rfl, rfl, rfl⟩, ⟨⟨rfl, rfl, rfl⟩, rfl⟩⟩
  | t10 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t11 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t12 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t13 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t14 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t15 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t16 => exact rfl
  | t17 => exact rfl
  | t18 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t19 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t20 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t21 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t22 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t23 => exact rfl
  | t24 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩
  | t25 => exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

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
  | 0 => [Tok.t24]
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

theorem wLen_rec (t : Tok) : wLen 7 t = 2 * wLen 6 t - wLen 4 t := by
  cases t <;> decide

theorem listSum_rec : ∀ ts : List Tok, listSum (wLen 7) ts = 2 * listSum (wLen 6) ts - listSum (wLen 4) ts
  | [] => rfl
  | t :: ts => by
    have ht := wLen_rec t
    have ih := listSum_rec ts
    simp only [listSum]
    linear_combination ht + ih

theorem len_rec (n : ℕ) : ((w (n + 7)).length : ℤ) = 2 * ((w (n + 6)).length : ℤ) - ((w (n + 4)).length : ℤ) := by
  rw [len_w_add 4 n]
  rw [len_w_add 6 n]
  rw [len_w_add 7 n]
  exact listSum_rec (toks n)

theorem base_eq (k : ℕ) (hk : k < 7) : ((w k).length : ℤ) = A289107 k := by
  have h0 : ((w (0 + k)).length : ℤ) = listSum (wLen k) (toks 0) := len_w_add k 0
  rw [Nat.zero_add] at h0
  rw [h0]
  interval_cases k <;> decide

theorem len_eq : ∀ n : ℕ,
    ((w n).length : ℤ) = A289107 n ∧
    ((w (n + 1)).length : ℤ) = A289107 (n + 1) ∧
    ((w (n + 2)).length : ℤ) = A289107 (n + 2) ∧
    ((w (n + 3)).length : ℤ) = A289107 (n + 3) ∧
    ((w (n + 4)).length : ℤ) = A289107 (n + 4) ∧
    ((w (n + 5)).length : ℤ) = A289107 (n + 5) ∧
    ((w (n + 6)).length : ℤ) = A289107 (n + 6)
  | 0 => ⟨base_eq 0 (by omega), base_eq 1 (by omega), base_eq 2 (by omega), base_eq 3 (by omega), base_eq 4 (by omega), base_eq 5 (by omega), base_eq 6 (by omega)⟩
  | n + 1 => by
    obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := len_eq n
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    show ((w (n + 7)).length : ℤ) = A289107 (n + 7)
    have hA : A289107 (n + 7) = 2 * A289107 (n + 6) - A289107 (n + 4) := rfl
    rw [hA, ← h6, ← h4]
    exact len_rec n

end A289104Proof

open OMA.S_oeis_a289104 A289104Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a289104.main := by
  intro n
  exact (len_eq n).1
