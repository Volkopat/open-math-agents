import OMAStatements.S_mo_40561

/- Adapted from OpenAI, https://github.com/openai/math at 3344da59991ed94f9ba711217b29c1d760badfa6. Selected and combined Hirsch modules; adapted for Lean 4.33.1.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

-- Terms
noncomputable section

namespace OAI.Geometry.Hirsch.Layer

structure World (X : Type) (n : ℕ) where
  layer : X → ℕ
  bound : ∀ x, layer x < n
  live : X → Prop
  step : X → Bool → X
  west : ∀ x, live x → layer (step x false) + 1 = layer x
  east : ∀ x, live x → layer (step x true) = layer x + 1
  rank : X → ℕ
  decrease : ∀ x, live x → ∀ d, rank (step x d) < rank x

namespace World

variable {X : Type} {n : ℕ} (w : World X n)

def Full : Prop :=
  (∀ j < n, ∃ x, w.layer x = j) ∧
  ∀ x y, w.layer x + 2 = w.layer y →
    ∃ z, w.live z ∧ w.step z false = x ∧ w.step z true = y

inductive Shape where
  | tip
  | fork (west east : Shape)

def Shape.depth : Shape → ℕ
  | .tip => 0
  | .fork a b => max a.depth b.depth + 1

abbrev Term (n : ℕ) := Fin n × Shape

def freeStep : Term n → Bool → Term n
  | (i,.tip),_ => (i,.tip)
  | (i,.fork a _),false => (⟨i.val-1,by omega⟩,a)
  | (i,.fork _ b),true => (⟨min (i.val+1) (n-1),by have := i.isLt; omega⟩,b)

def free (n : ℕ) : World (Term n) n where
  layer x := x.1.val
  bound x := x.1.isLt
  live x := x.2 ≠ .tip ∧ 0 < x.1.val ∧ x.1.val+1 < n
  step := freeStep
  west := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh <;> simp_all [freeStep]; omega
  east := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh <;> simp_all [freeStep]; omega
  rank x := x.2.depth
  decrease := by rintro ⟨i,_ | ⟨a,b⟩⟩ hh (_ | _) <;> simp_all [freeStep,Shape.depth]

theorem full_free (n : ℕ) : (free n).Full := by
  refine ⟨fun j hj => ⟨(⟨j,hj⟩,.tip),rfl⟩,?_⟩
  rintro ⟨i,a⟩ ⟨j,b⟩ hh
  change i.val+2 = j.val at hh
  refine ⟨(⟨i.val+1,by omega⟩,.fork a b),?_,?_,?_⟩
  · simp [free]; omega
  · simp [free,freeStep]
  · simp [free,freeStep,Fin.ext_iff]; omega

def turn (d e : Bool) : ℕ := if d = e then 0 else 1

inductive Walk (ok stop : X → Prop) : X → Bool → ℕ → Prop
  | done {x d k} (good : ok x) (last : stop x) : Walk ok stop x d k
  | go {x d e k m} (good : ok x) (live : w.live x) (budget : m + turn d e ≤ k)
      (tail : Walk ok stop (w.step x e) e m) : Walk ok stop x d k

abbrev Escape (ok : X → Prop) := w.Walk ok (fun x => ¬w.live x)

variable {w} {ok stop ok' stop' : X → Prop} {x : X} {d : Bool} {k : ℕ}

theorem Walk.good (hw : w.Walk ok stop x d k) : ok x := by cases hw <;> assumption

theorem Walk.mono (hw : w.Walk ok stop x d k) (ho : ∀ x, ok x → ok' x)
    (hs : ∀ x, stop x → stop' x) : w.Walk ok' stop' x d k := by
  induction hw with
  | done hg hl => exact .done (ho _ hg) (hs _ hl)
  | go hg hl hb _ ih => exact .go (ho _ hg) hl hb ih

theorem Walk.more (hw : w.Walk ok stop x d k) {m : ℕ} (hm : k ≤ m) : w.Walk ok stop x d m := by
  cases hw with
  | done hg hl => exact .done hg hl
  | go hg hl hb ht => exact .go hg hl (hb.trans hm) ht

theorem Walk.redirect (hw : w.Walk ok stop x d k) (e : Bool) : w.Walk ok stop x e (k+1) := by
  cases hw with
  | done hg hl => exact .done hg hl
  | go hg hl hb ht =>
    refine .go hg hl ?_ ht
    unfold turn at *
    split <;> omega

theorem Walk.append (hw : w.Walk ok stop x d k) {m : ℕ}
    (hs : ∀ x, stop x → ∀ d, w.Walk ok stop' x d m) : w.Walk ok stop' x d (k+m) := by
  induction hw with
  | done _ hl => exact (hs _ hl _).more (by omega)
  | go hg hl hb _ ih => exact .go hg hl (by omega) ih

theorem induct (w : World X n) (p : X → Prop)
    (step : ∀ x, (w.live x → ∀ d, p (w.step x d)) → p x) : ∀ x, p x := by
  intro x
  induction x using (measure w.rank).wf.induction with
  | h x ih => exact step x (fun hl d => ih _ (w.decrease x hl d))

def distance (n j : ℕ) (d : Bool) := if d then n-1-j else j

def cost (n j : ℕ) (d : Bool) (k : ℕ) := k*n + distance n j d

theorem distance_lt (w : World X n) (x : X) (d : Bool) : distance n (w.layer x) d < n := by
  have := w.bound x
  unfold distance
  split <;> omega

theorem cost_step (hl : w.live x) {e : Bool} {m : ℕ} (hb : m + turn d e ≤ k) :
    cost n (w.layer (w.step x e)) e m < cost n (w.layer x) d k := by
  unfold cost
  by_cases he : d = e
  · subst e
    have hm := Nat.mul_le_mul_right n (show m ≤ k by simpa [turn] using hb)
    have h₁ := w.west x hl
    have h₂ := w.east x hl
    have h₃ := w.bound (w.step x true)
    cases d <;> simp only [distance,Bool.false_eq_true,↓reduceIte] <;> omega
  · have hm := Nat.mul_le_mul_right n (show m+1 ≤ k by simpa [turn,he] using hb)
    rw [add_mul,one_mul] at hm
    have := w.distance_lt (w.step x e) e
    omega

end World
end OAI.Geometry.Hirsch.Layer
end

-- Readings
noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Index : Type} [Fintype Index] [Nonempty Index]

def least (values : Index → ℝ) := Finset.univ.inf' Finset.univ_nonempty values

theorem least_le (values : Index → ℝ) (idx : Index) : least values ≤ values idx :=
  Finset.inf'_le values (Finset.mem_univ idx)

theorem le_least {values : Index → ℝ} {lower : ℝ} (hh : ∀ idx, lower ≤ values idx) :
    lower ≤ least values :=
  Finset.le_inf' _ _ (fun idx _ => hh idx)

theorem least_attained (values : Index → ℝ) : ∃ idx, least values = values idx := by
  obtain ⟨idx, _, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty values
  exact ⟨idx, he⟩

end OAI.Geometry.Hirsch
end

-- PathSlack
noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer.World

variable {X : Type} {n V : ℕ} (w : World X n) (D : ℕ) (ok : Fin V → X → Prop)

abbrev Mode (D : ℕ) := Bool × Fin (D+1)

def weight (n j : ℕ) (p : Mode D) := (1/4 : ℝ) ^ cost n j p.1 p.2

def entry (x : X) (l : Fin V) (p : Mode D) : ℝ := by
  classical
  exact if w.Escape (ok l) x p.1 p.2 then weight D n (w.layer x) p else 0

def slack (x : X) (l : Fin V) := -least (fun p => -w.entry D ok x l p)

theorem entry_le (x : X) (l : Fin V) (p : Mode D) : w.entry D ok x l p ≤ w.slack D ok x l := by
  unfold slack
  linarith [least_le (fun p => -w.entry D ok x l p) p]

theorem attained (x : X) (l : Fin V) : ∃ p, w.slack D ok x l = w.entry D ok x l p := by
  obtain ⟨p,hp⟩ := least_attained (fun p => -w.entry D ok x l p)
  exact ⟨p,by simp [slack,hp]⟩

theorem slack_nonneg (x : X) : 0 ≤ w.slack D ok x := by
  intro l
  obtain ⟨p,hp⟩ := w.attained D ok x l
  rw [hp]
  change 0 ≤ _
  unfold entry weight
  split <;> positivity

theorem slack_zero {x : X} {l : Fin V} (hn : ¬ok l x) : w.slack D ok x l = 0 := by
  obtain ⟨p,hp⟩ := w.attained D ok x l
  have hh : ¬w.Escape (ok l) x p.1 p.2 := fun he => hn he.good
  simp [hp,entry,hh]

theorem slack_pos {x : X} {l : Fin V} {d : Bool} (hw : w.Escape (ok l) x d D) :
    0 < w.slack D ok x l := by
  apply lt_of_lt_of_le _ (w.entry_le D ok x l (d,⟨D,by omega⟩))
  simp only [entry,hw,↓reduceIte,weight]
  positivity

theorem slack_merge {x : X} (hx : w.live x) (l : Fin V) :
    w.slack D ok x l ≤ (1/4 : ℝ) * max (w.slack D ok (w.step x false) l) (w.slack D ok (w.step x true) l) := by
  obtain ⟨⟨d,k⟩,he⟩ := w.attained D ok x l
  rw [he,entry]
  split
  · rename_i hw
    cases hw with
    | done _ hh => contradiction
    | @go _ _ e _ m _ _ hb ht =>
      have hm : m < D+1 := by have := k.isLt; omega
      let p : Mode D := (e,⟨m,hm⟩)
      have hs : weight D n (w.layer (w.step x e)) p ≤ w.slack D ok (w.step x e) l := by
        simpa [entry,p,ht] using w.entry_le D ok (w.step x e) l p
      have hc := cost_step hx hb
      calc
        _ ≤ (1/4 : ℝ) ^ (cost n (w.layer (w.step x e)) e m + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
        _ = (1/4 : ℝ) * weight D n (w.layer (w.step x e)) p := pow_succ' ..
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left (hs.trans ?_) (by norm_num)
          cases e
          · exact le_max_left ..
          · exact le_max_right ..
  · exact mul_nonneg (by norm_num) ((w.slack_nonneg D ok _ l).trans (le_max_left ..))

end OAI.Geometry.Hirsch.Layer.World
end

-- StateSequence (micro)
noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {L k : ℕ}

def micro (s : Fin L) (j : Fin k) := s.val*(k+2)+1+j.val

theorem micro_bound (s : Fin L) (j : Fin k) : micro s j < L*(k+2) := by
  have hh := Nat.mul_le_mul_right (k+2) s.isLt
  unfold micro
  nlinarith [j.isLt]

theorem micro_lt {s t : Fin L} (hs : s < t) (i j : Fin k) : micro s i < micro t j := by
  have hh := Nat.mul_le_mul_right (k+2) hs
  unfold micro
  nlinarith [i.isLt]

end OAI.Geometry.Hirsch.Layer
end

-- Emissions
noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {X A : Type} {L k V D : ℕ}

namespace World

variable (w : World X (L*(k+2)))

def site (x : X) : Fin L :=
  ⟨w.layer x / (k+2),(Nat.div_lt_iff_lt_mul (by omega)).mpr (w.bound x)⟩

theorem site_micro {x : X} {s : Fin L} {j : Fin k} (hx : w.layer x = micro s j) : w.site x = s := by
  apply Fin.ext
  simp only [site,hx,micro,add_assoc]
  rw [mul_comm s.val, Nat.mul_add_div (by omega : 0 < k+2),Nat.div_eq_of_lt (by omega),add_zero]

def Away (t : Fin L) (d : Bool) (x : X) := if d then t < w.site x else w.site x < t

theorem away_ne {t d x} (ha : w.Away t d x) : t ≠ w.site x := by
  cases d
  · exact ne_of_gt ha
  · exact ne_of_lt ha

theorem away_step {t d x} (ha : w.Away t d x) (hl : w.live x) : w.Away t d (w.step x d) := by
  cases d
  · have hh : w.site (w.step x false) ≤ w.site x :=
      Nat.div_le_div_right (by have := w.west x hl; omega)
    exact lt_of_le_of_lt hh ha
  · have hh : w.site x ≤ w.site (w.step x true) :=
      Nat.div_le_div_right (by have := w.east x hl; omega)
    exact lt_of_lt_of_le ha hh

structure Emissions (A : Type) (D : ℕ) where
  emit : X → Option A
  micro : ∀ (s : Fin L) (j : Fin k) x, w.layer x = Layer.micro s j → ∃ i, emit x = some i
  escape : ∀ x i, emit x = some i → ∀ d, w.Escape (fun y => emit y = some i → w.site y = w.site x) x d D

end World

end OAI.Geometry.Hirsch.Layer
end

-- Palette
noncomputable section

namespace OAI.Geometry.Hirsch.Layer

def PaletteTheorem : Prop :=
  ∀ m : ℕ, 0 < m → ∀ threshold : ℕ, ∃ b D : ℕ, 2 ≤ b ∧ threshold ≤ b ∧
    ∀ k, 0 < k → Nonempty ((World.free (b^m*(k+2))).Emissions (Fin b) D)

end OAI.Geometry.Hirsch.Layer
end

-- Law
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

structure Law (Ω : Type) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

namespace Law

variable {Ω I : Type} [Fintype Ω] (p : Law Ω)

def prob (e : Ω → Prop) := ∑ x, if e x then p.mass x else 0

theorem positive (e : Ω → Prop) : 0 ≤ p.prob e :=
  Finset.sum_nonneg (fun x _ => by split <;> simp [p.nonneg])

theorem mono {e f : Ω → Prop} (h : ∀ x, e x → f x) : p.prob e ≤ p.prob f := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hh : e x
  · simp [hh,h x hh]
  · simp [hh]; split <;> simp [p.nonneg]

theorem certain {e : Ω → Prop} (h : ∀ x, e x) : p.prob e = 1 := by simp [prob,h,p.total]

theorem neg (e : Ω → Prop) : p.prob (fun x => ¬e x) = 1 - p.prob e := by
  rw [eq_sub_iff_add_eq,prob,prob,← Finset.sum_add_distrib,← p.total]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : e x <;> simp [hh]

theorem witness {e : Ω → Prop} (h : p.prob e < 1) : ∃ x, ¬e x := by
  by_contra! hn
  exact h.ne (p.certain hn)

theorem union [Fintype I] (e : I → Ω → Prop) :
    p.prob (fun x => ∃ i, e i x) ≤ ∑ i, p.prob (e i) := by
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hn : ∀ i, 0 ≤ if e i x then p.mass x else 0 := fun i => by split <;> simp [p.nonneg]
  split
  · rename_i h
    obtain ⟨i,hi⟩ := h
    simpa [hi] using Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
  · exact Finset.sum_nonneg (fun j _ => hn j)

variable [Fintype I] [DecidableEq I] {X : I → Type} [∀ i, Fintype (X i)]

def product (ps : ∀ i, Law (X i)) : Law (∀ i, X i) where
  mass x := ∏ i, (ps i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (ps i).nonneg (x i))
  total := by rw [← Fintype.prod_sum]; simp [total]

theorem independent (ps : ∀ i, Law (X i)) (e : ∀ i, X i → Prop) :
    (product ps).prob (fun x => ∀ i, e i (x i)) = ∏ i, (ps i).prob (e i) := by
  unfold prob
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hh : ∀ i, e i (x i)
  · simp [hh,product]
  · obtain ⟨i,hi⟩ := not_forall.mp hh
    simp only [hh,↓reduceIte]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

def copies (p : Law Ω) (n : ℕ) : Law (Fin n → Ω) := product (fun _ => p)

theorem miss (n : ℕ) (e : Ω → Prop) :
    (p.copies n).prob (fun x => ∀ i, ¬e (x i)) ≤ Real.exp (-(n : ℝ)*p.prob e) := by
  have he := independent (fun _ : Fin n => p) (fun _ x => ¬e x)
  change (p.copies n).prob _ = _ at he
  rw [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin,neg_mul,← mul_neg,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (p.positive _)
  rw [p.neg]
  linarith [Real.add_one_le_exp (-p.prob e)]

omit [DecidableEq I] in
theorem hitting (n : ℕ) (e : I → Ω → Prop) (bound : ℝ)
    (he : ∀ i, bound ≤ p.prob (e i))
    (hn : Fintype.card I * Real.exp (-(n : ℝ)*bound) < 1) :
    ∃ x : Fin n → Ω, ∀ i, ∃ j, e i (x j) := by
  let bad := fun i (x : Fin n → Ω) => ∀ j, ¬e i (x j)
  have hb : ∀ i, (p.copies n).prob (bad i) ≤ Real.exp (-(n : ℝ)*bound) := fun i =>
    (p.miss n (e i)).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (he i) (by simp)))
  have hh := ((p.copies n).union bad).trans (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  obtain ⟨x,hx⟩ := (p.copies n).witness (hh.trans_lt hn)
  exact ⟨x,fun i => by by_contra! h; exact hx ⟨i,h⟩⟩

end Law
end OAI.Geometry.Hirsch.Layer
end

-- Hitting
noncomputable section

open Classical Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer.Law

variable {Ω : Type} [Fintype Ω] (p : Law Ω) (c : ℕ)

def Hits (h : ℕ) (sample : Fin ((2*c)^h) → Fin h → Ω) : Prop :=
  ∀ P : Fin h → Set Ω, (∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i)) → ∃ j, ∀ i, sample j i ∈ P i

theorem many_samples (hc : 0 < c) :
    ∀ᶠ h : ℕ in atTop, ∃ sample, p.Hits c h sample := by
  have ht : Tendsto (fun h : ℕ => (h : ℝ) / (2 : ℝ)^h * Fintype.card Ω) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 1 (r := 2) (by norm_num)).mul_const
      (Fintype.card Ω : ℝ)
  filter_upwards [ht.eventually (eventually_lt_nhds zero_lt_one)] with h hh
  let I := {P : Fin h → Set Ω // ∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i)}
  let event := fun (P : I) (x : Fin h → Ω) => ∀ i, x i ∈ P.val i
  have he : ∀ P, (c : ℝ)⁻¹^h ≤ (p.copies h).prob (event P) := by
    intro P
    change _ ≤ (product _).prob (fun x => ∀ i, x i ∈ P.val i)
    rw [independent (fun _ : Fin h => p) (fun i x => x ∈ P.val i)]
    simpa using Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity : ∀ i : Fin h,
      i ∈ Finset.univ → 0 ≤ (c : ℝ)⁻¹) (fun i _ => P.property i)
  have hn : Fintype.card I ≤ 2^(Fintype.card Ω*h) := by
    simpa [I,pow_mul] using Fintype.card_subtype_le (fun P : Fin h → Set Ω =>
      ∀ i, (c : ℝ)⁻¹ ≤ p.prob (· ∈ P i))
  have hpow : (Fintype.card Ω*h : ℕ) < (2 : ℝ)^h := by
    rw [div_mul_eq_mul_div,div_lt_one (by positivity)] at hh
    simpa [mul_comm] using hh
  have hmul : -(((2*c)^h : ℕ) : ℝ) * (c : ℝ)⁻¹^h = -(2 : ℝ)^h := by
    have hn : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    simp [neg_mul,mul_pow,hn]
  have hcnt : Fintype.card I * Real.exp (-(((2*c)^h : ℕ) : ℝ) * (c : ℝ)⁻¹^h) < 1 := by
    rw [hmul,Real.exp_neg,← div_eq_mul_inv,div_lt_one (Real.exp_pos _)]
    apply lt_of_le_of_lt _ (Real.exp_lt_exp.mpr hpow)
    calc
      _ ≤ (2 : ℝ)^(Fintype.card Ω*h) := by exact_mod_cast hn
      _ ≤ (Real.exp 1)^(Fintype.card Ω*h) := by gcongr; linarith [Real.add_one_le_exp 1]
      _ = _ := by rw [← Real.exp_nat_mul,mul_one]
  obtain ⟨sample,hs⟩ := (p.copies h).hitting ((2*c)^h) event _ he hcnt
  exact ⟨sample,fun P hp => hs ⟨P,hp⟩⟩

end OAI.Geometry.Hirsch.Layer.Law
end

-- Grid
noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

variable {X : Type} {n : ℕ} (w : World X n)

def Blank (width : ℕ) (x : X) := width ∣ w.layer x ∨ width ∣ w.layer x + 1

def block (width : ℕ) (x : X) := w.layer x / width

theorem blank_mono {a b : ℕ} (hab : a ∣ b) {x : X} (hx : w.Blank b x) : w.Blank a x :=
  hx.imp hab.trans hab.trans

theorem boundary {x : X} (hx : w.Blank n x) : ¬ w.live x := by
  intro hl
  have h₁ := w.west x hl
  have h₂ := w.east x hl
  have h₃ := w.bound (w.step x true)
  rcases hx with hx | hx <;> have := Nat.le_of_dvd (by omega) hx <;> omega

theorem blank_micro {L k : ℕ} {s : Fin L} {j : Fin k} {x : X} (hx : w.layer x = micro s j) :
    ¬w.Blank (k+2) x := by
  unfold Blank
  rw [hx,micro]
  simp only [add_assoc,Nat.dvd_iff_mod_eq_zero,Nat.mul_add_mod_self_right]
  rw [Nat.mod_eq_of_lt (by omega : 1+j.val < k+2),Nat.mod_eq_of_lt (by omega : 1+(j.val+1) < k+2)]
  omega

theorem parent (width base : ℕ) (x : X) :
    w.block (width*base) x = w.block width x / base := (Nat.div_div_eq_div_mul ..).symm

theorem same_step {width : ℕ} {x : X} (hl : w.live x) (hn : ¬w.Blank width x) (d : Bool) :
    w.block width (w.step x d) = w.block width x := by
  have hs : ∀ a : ℕ, ¬ width ∣ a+1 → (a+1)/width = a/width := by
    intro a ha
    exact Nat.succ_div_of_not_dvd ha
  cases d
  · unfold block
    have hw := w.west x hl
    rw [← hw]
    exact (hs _ (fun h => hn (Or.inl (hw ▸ h)))).symm
  · unfold block
    rw [w.east x hl]
    exact hs _ (fun h => hn (Or.inr h))

theorem spine (width : ℕ) (d : Bool) : ∀ x,
    w.Walk (fun y => w.block width y = w.block width x)
      (fun y => ¬w.live y ∨ w.Blank width y) x d 0 := by
  apply w.induct
  intro x ih
  by_cases hl : w.live x
  swap
  · exact .done rfl (.inl hl)
  by_cases hb : w.Blank width x
  · exact .done rfl (.inr hb)
  have ht := ih hl d
  rw [w.same_step hl hb d] at ht
  exact .go rfl hl (by simp [turn]) ht

theorem Walk.endpoint {w : World X n} {ok stop : X → Prop} {x d k} (hw : w.Walk ok stop x d k) :
    ∃ y, ok y ∧ stop y ∧ w.Walk ok (· = y) x d k := by
  induction hw with
  | done hg hl => exact ⟨_,hg,hl,.done hg rfl⟩
  | go hg hl hb _ ih =>
    obtain ⟨y,hy,hs,ht⟩ := ih
    exact ⟨y,hy,hs,.go hg hl hb ht⟩

def digit (width base : ℕ) [NeZero base] (x : X) : Fin base :=
  ⟨w.block width x % base,Nat.mod_lt _ (NeZero.pos base)⟩

theorem index_inj {width base : ℕ} [NeZero base] {x y : X}
    (hp : w.block (width*base) x = w.block (width*base) y)
    (hd : w.digit width base x = w.digit width base y) : w.block width x = w.block width y := by
  rw [parent,parent] at hp
  have hm : w.block width x % base = w.block width y % base := congrArg Fin.val hd
  exact (Nat.mod_add_div _ _).symm.trans (by rw [hp,hm,Nat.mod_add_div])

structure Potential {Ω : Type} [Fintype Ω] (p : Law Ω) (chance D width base : ℕ) where
  sets : X → Set Ω
  dense : ∀ x, ¬w.Blank width x → (chance : ℝ)⁻¹ ≤ p.prob (· ∈ sets x)
  path : ∀ x, w.Blank width x → ∀ a : Ω, ∃ j ≠ w.block width x,
    w.Walk (fun y => w.block (width*base) y = w.block (width*base) x ∧
      (a ∈ sets y → w.block width y = j))
      (fun y => ¬w.live y ∨ w.Blank (width*base) y) x false D

end OAI.Geometry.Hirsch.Layer.World
end

-- Multiscale
noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

variable {X Ω : Type} [Fintype Ω] {D base bits chance h k : ℕ} [NeZero base] [NeZero bits]
  {p : Law Ω} {w : World X (base^h*(k+2))}

def width (base k i : ℕ) := base^i*(k+2)

theorem width_next (base k i : ℕ) : width base k (i+1) = width base k i * base := by
  simp only [width,pow_succ]; ring

def Hierarchy (w : World X (base^h*(k+2))) (p : Law Ω) (chance D : ℕ) :=
  ∀ i : Fin h, w.Potential p chance D (width base k i) base

abbrev Address (base bits : ℕ) := Fin base ↪ (Fin bits → Bool)

def read (w : World X (base^h*(k+2))) (key : Address base bits) (i : Fin h) (x : X) :=
  key (w.digit (width base k i) base x)

namespace Hierarchy

variable (seq : Hierarchy w p chance D) (key : Address base bits) (x : X) (tuple : Fin h → Ω)

def Excludes (mask : Fin h → Fin bits) (low : ℕ) (y : X) :=
  w.Blank (k+2) y ∨ ∃ i : Fin h, low ≤ i.val ∧
    (tuple i ∉ (seq i).sets y ∨ w.read key i y (mask i) ≠ w.read key i x (mask i))

theorem distinguish (i : Fin h) (j : ℕ) (hj : j ≠ w.block (width base k i) x) :
    ∃ b, ∀ y, w.block (width base k (i.val+1)) y = w.block (width base k (i.val+1)) x →
      w.block (width base k i) y = j → w.read key i y b ≠ w.read key i x b := by
  classical
  let P := fun y => w.block (width base k (i.val+1)) y = w.block (width base k (i.val+1)) x ∧
    w.block (width base k i) y = j
  by_cases he : ∃ y, P y
  swap
  · exact ⟨0,fun y hp hs => (he ⟨y,hp,hs⟩).elim⟩
  obtain ⟨y,hp,hs⟩ := he
  have hn : w.read key i y ≠ w.read key i x := by
    intro hh
    rw [width_next] at hp
    exact hj (hs.symm.trans (w.index_inj hp (key.injective hh)))
  obtain ⟨b,hb⟩ := Function.ne_iff.mp hn
  refine ⟨b,fun z _ hz => ?_⟩
  simpa only [read,digit,hz,hs] using hb

theorem from_blank (low : ℕ) (hl : low ≤ h) (y : X) (hy : w.Blank (width base k low) y)
    (he : w.block (width base k low) y = w.block (width base k low) x) :
    ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask low) y d ((h-low)*(D+1)) := by
  classical
  induction hl using Nat.decreasingInduction generalizing y with
  | self =>
    have hb := w.blank_mono (dvd_mul_left (k+2) (base^h)) hy
    exact ⟨fun _ => 0,fun _ => .done (.inl hb) (w.boundary hy)⟩
  | of_succ low hl ih =>
    let i : Fin h := ⟨low,hl⟩
    obtain ⟨j,hj,path⟩ := (seq i).path y hy (tuple i)
    have he' : w.block (width base k (low+1)) y = w.block (width base k (low+1)) x := by
      rw [width_next,parent,parent,he]
    obtain ⟨b,hb⟩ := distinguish key x i j (fun h => hj (h.trans he.symm))
    rw [← width_next] at path
    obtain ⟨z,hz,hs,hw⟩ := path.endpoint
    let rest := (h-(low+1))*(D+1)
    have more : ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask (low+1)) z d rest ∨ ¬w.live z := by
      rcases hs with hs | hs
      · exact ⟨fun _ => 0,fun _ => .inr hs⟩
      · obtain ⟨mask,hm⟩ := ih z hs (hz.1.trans he')
        exact ⟨mask,fun d => .inl (hm d)⟩
    obtain ⟨mask,hm⟩ := more
    let updated := Function.update mask i b
    let good := seq.Excludes key x tuple updated low
    have here : ∀ u, w.block (width base k (low+1)) u = w.block (width base k (low+1)) y ∧
        (tuple i ∈ (seq i).sets u → w.block (width base k low) u = j) → good u := by
      rintro u ⟨hp,hm⟩
      refine .inr ⟨i,le_rfl,?_⟩
      by_cases hu : tuple i ∈ (seq i).sets u
      · exact .inr (by simpa [updated] using hb u (hp.trans he') (hm hu))
      · exact .inl hu
    have later : ∀ u, seq.Excludes key x tuple mask (low+1) u → good u := by
      rintro u (hb | ⟨a,ha,hm⟩)
      · exact .inl hb
      · have hn : a ≠ i := by intro he; subst a; change low+1 ≤ low at ha; omega
        exact .inr ⟨a,by omega,by simpa [updated,hn] using hm⟩
    have endpath : ∀ u, u = z → ∀ d, w.Escape good u d rest := by
      rintro _ rfl d
      rcases hm d with ht | ht
      · exact ht.mono later (fun _ h => h)
      · exact .done (here _ hz) ht
    refine ⟨updated,fun d => ?_⟩
    have walk := (((hw.mono here (fun _ h => h)).redirect d).append endpath)
    apply walk.more
    unfold rest
    rw [show h-low = 1+(h-(low+1)) by omega,add_mul,one_mul]

theorem escape : ∃ mask, ∀ d, w.Escape
    (fun y => w.site y = w.site x ∨ seq.Excludes key x tuple mask 0 y) x d (h*(D+1)+1) := by
  obtain ⟨y,hy,hs,hw⟩ := (w.spine (k+2) false x).endpoint
  have more : ∃ mask, ∀ d, w.Escape (seq.Excludes key x tuple mask 0) y d (h*(D+1)) ∨ ¬w.live y := by
    rcases hs with hs | hs
    · exact ⟨fun _ => 0,fun _ => .inr hs⟩
    · obtain ⟨mask,hm⟩ := seq.from_blank key x tuple 0 (by omega) y (by simpa [width] using hs)
        (by simpa [width] using hy)
      exact ⟨mask,fun d => .inl (hm d)⟩
  obtain ⟨mask,hm⟩ := more
  let good := fun y => w.site y = w.site x ∨ seq.Excludes key x tuple mask 0 y
  have start : w.Walk good (· = y) x false 0 :=
    hw.mono (fun _ hh => .inl (Fin.ext hh)) (fun _ hh => hh)
  have finish : ∀ u, u = y → ∀ d, w.Escape good u d (h*(D+1)) := by
    rintro _ rfl d
    rcases hm d with ht | ht
    · exact ht.mono (fun _ hh => .inr hh) (fun _ hh => hh)
    · exact .done (.inl (Fin.ext hy)) ht
  exact ⟨mask,fun d => ((start.append finish).redirect d).more (by omega)⟩

end Hierarchy
end OAI.Geometry.Hirsch.Layer.World
end

-- Primary
noncomputable section

open Set Filter

namespace OAI.Geometry.Hirsch.Layer

namespace World

variable {X Ω : Type} [Fintype Ω] {D base bits chance h k : ℕ} [NeZero base] [NeZero bits]
  {p : Law Ω} {w : World X (base^h*(k+2))}

abbrev Color (chance bits h : ℕ) := Fin ((2*chance)^h) × (Fin h → Fin bits × Bool)

theorem Hierarchy.color (seq : Hierarchy w p chance D) (key : Address base bits) (hc : 0 < chance)
    {sample : Fin ((2*chance)^h) → Fin h → Ω} (hit : p.Hits chance h sample) :
    Nonempty (w.Emissions (Color chance bits h) (h*(D+1)+1)) := by
  classical
  have chooseTuple : ∀ x, ∃ j, ¬w.Blank (k+2) x → ∀ i, sample j i ∈ (seq i).sets x := by
    intro x
    by_cases hx : w.Blank (k+2) x
    · exact ⟨⟨0,by positivity⟩,fun hn => (hn hx).elim⟩
    obtain ⟨j,hj⟩ := hit (fun i => (seq i).sets x) (fun i =>
      (seq i).dense x (fun hh => hx (w.blank_mono (dvd_mul_left ..) hh)))
    exact ⟨j,fun _ => hj⟩
  choose idx hidx using chooseTuple
  choose mask hmask using fun x => seq.escape key x (sample (idx x))
  let color : X → Color chance bits h := fun x =>
    (idx x,fun i => (mask x i,w.read key i x (mask x i)))
  let emit := fun x => if w.Blank (k+2) x then none else some (color x)
  have emits : ∀ x i, emit x = some i → ¬w.Blank (k+2) x ∧ color x = i := by
    intro x i
    by_cases hx : w.Blank (k+2) x <;> simp [emit,hx]
  refine ⟨⟨emit,fun s j x hx => ⟨color x,by simp [emit,w.blank_micro hx]⟩,fun x i hi d => ?_⟩⟩
  apply (hmask x d).mono _ (fun _ hh => hh)
  intro y hy he
  obtain ⟨hn,hy'⟩ := emits y _ he
  have same : color y = color x := hy'.trans (emits x _ hi).2.symm
  rcases hy with hy | hy | ⟨j,_,hh⟩
  · exact hy
  · exact (hn hy).elim
  · have hj : idx y = idx x := congrArg Prod.fst same
    have he := congrFun (congrArg Prod.snd same) j
    obtain ⟨hm,hv⟩ := Prod.mk.inj he
    rcases hh with hh | hh
    · exact (hh (hj ▸ hidx y hn j)).elim
    · rw [hm] at hv
      exact (hh hv).elim

theorem Emissions.map {X A B : Type} {L k D : ℕ} {w : World X (L*(k+2))}
    (col : w.Emissions A D) (f : A ↪ B) : Nonempty (w.Emissions B D) := by
  refine ⟨⟨fun x => (col.emit x).map f,?_,?_⟩⟩
  · intro s j x hx
    obtain ⟨a,ha⟩ := col.micro s j x hx
    exact ⟨f a,by simp [ha]⟩
  · intro x b hb d
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hb
    apply (col.escape x a ha d).mono _ (fun _ hh => hh)
    intro y hy he
    obtain ⟨c,hc,he⟩ := Option.map_eq_some_iff.mp he
    exact hy (f.injective he ▸ hc)

end World

def PrimaryLemma : Prop :=
  ∀ m : ℕ, 0 < m → ∃ b bits chance D : ℕ, 2 ≤ b ∧ 0 < bits ∧ 0 < chance ∧
    b^m ≤ 2^bits ∧ (2*chance)*(bits*2) ≤ b ∧
    ∃ (Ω : Type) (_ : Fintype Ω) (p : Law Ω), ∀ (X : Type) n (w : World X n) width,
      3 ≤ width → Nonempty (w.Potential p chance D width (b^m))

theorem palette_of_primary (input : PrimaryLemma) : PaletteTheorem := by
  intro m hm threshold
  obtain ⟨b,bits,chance,D,hb,hbits,hc,hkey,hsize,Ω,inst,p,hs⟩ := input m hm
  let : NeZero (b^m) := ⟨by positivity⟩
  let : NeZero bits := ⟨hbits.ne'⟩
  let key : World.Address (b^m) bits :=
    (Fin.castLEEmb (by simpa using hkey : b^m ≤ Fintype.card (Fin bits → Bool))).trans
      (Fintype.equivFin _).symm.toEmbedding
  obtain ⟨h,hh,sample,hit⟩ := ((eventually_gt_atTop threshold).and (p.many_samples chance hc)).exists
  have hbig : h < b^h := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hb _)
  refine ⟨b^h,h*(D+1)+1,by omega,by omega,fun k hk => ?_⟩
  have he : (b^h)^m = (b^m)^h := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [he]
  let w := World.free ((b^m)^h*(k+2))
  let seq : World.Hierarchy w p chance D := fun i =>
    Classical.choice (hs _ _ w _ ((show 3 ≤ k+2 by omega).trans (Nat.le_mul_of_pos_left _ (by positivity))))
  obtain ⟨col⟩ := seq.color key hc hit
  have hcard : Fintype.card (World.Color chance bits h) ≤ b^h := by
    simpa [World.Color,mul_pow] using Nat.pow_le_pow_left hsize h
  exact col.map ((Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hcard))

end OAI.Geometry.Hirsch.Layer
end

-- Mean
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Law

variable {Ω I : Type} [Fintype Ω] (p : Law Ω)

def mean (f : Ω → ℝ) := ∑ x, p.mass x * f x

def ind (a : Prop) : ℝ := if a then 1 else 0

theorem ind_nonneg (a : Prop) : 0 ≤ ind a := by unfold ind; split <;> norm_num

@[simp] theorem ind_mul (a b : Prop) : ind a * ind b = ind (a ∧ b) := by
  by_cases h : a <;> simp [ind,h]

@[simp] theorem ind_sq (a : Prop) : ind a ^ 2 = ind a := by rw [pow_two,ind_mul,and_self]

theorem mean_mono {f g : Ω → ℝ} (hh : ∀ x, f x ≤ g x) : p.mean f ≤ p.mean g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hh x) (p.nonneg x))

theorem mean_congr {f g : Ω → ℝ} (hh : ∀ x, f x = g x) : p.mean f = p.mean g := congrArg p.mean (funext hh)

theorem eq_prob {e f : Ω → Prop} (hh : ∀ x, e x ↔ f x) : p.prob e = p.prob f :=
  congrArg p.prob (funext fun x => propext (hh x))

@[simp] theorem mean_ind (e : Ω → Prop) : p.mean (fun x => ind (e x)) = p.prob e := by
  simp [mean,ind,prob,mul_ite]

@[simp] theorem mean_const (a : ℝ) : p.mean (fun _ => a) = a := by simp [mean,← Finset.sum_mul,p.total]

theorem mean_add (f g : Ω → ℝ) : p.mean (fun x => f x + g x) = p.mean f + p.mean g := by
  simp [mean,mul_add,Finset.sum_add_distrib]

theorem mean_scale (a : ℝ) (f : Ω → ℝ) : p.mean (fun x => a * f x) = a * p.mean f := by
  simp [mean,mul_left_comm,Finset.mul_sum]

theorem mean_sum (s : Finset I) (f : I → Ω → ℝ) :
    p.mean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, p.mean (f i) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem mean_comm (f : Ω → Ω → ℝ) : p.mean (fun x => p.mean (f x)) = p.mean (fun y => p.mean (fun x => f x y)) := by
  simp only [mean,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

theorem mean_kernel (a : Ω → ℝ) (f : Ω → Ω → ℝ) :
    p.mean (fun y => a y * p.mean (fun x => f x y)) = p.mean (fun x => p.mean (fun y => a y * f x y)) := by
  rw [p.mean_comm (fun x y => a y * f x y)]
  simp only [mean_scale]

theorem restricted_le {e : Ω → Prop} {f : Ω → ℝ} {a : ℝ} (hh : ∀ x, e x → f x ≤ a) :
    p.mean (fun x => ind (e x) * f x) ≤ a * p.prob e := by
  rw [← mean_ind,← mean_scale]
  exact p.mean_mono fun x => by by_cases h : e x <;> simp [ind,h,hh]

theorem restricted_ge {e : Ω → Prop} {f : Ω → ℝ} {a : ℝ} (hh : ∀ x, e x → a ≤ f x) :
    a * p.prob e ≤ p.mean (fun x => ind (e x) * f x) := by
  rw [← mean_ind,← mean_scale]
  exact p.mean_mono fun x => by by_cases h : e x <;> simp [ind,h,hh]

theorem transfer (bad e : Ω → Prop) (kernel : Ω → Ω → ℝ) {u C : ℝ} (hu : 0 < u) (hc : 0 < C)
    (lower : ∀ x, bad x → u ≤ p.mean (fun y => ind (e y)*kernel x y))
    (upper : ∀ x, bad x → p.mean (fun z => ind (bad z)*p.mean (fun y => kernel x y*kernel z y)) ≤ C) :
    u^2 * p.prob bad ≤ C * p.prob e := by
  let F := fun y => p.mean (fun x => ind (bad x)*kernel x y)
  have aux : ∀ a : Ω → ℝ, p.mean (fun y => a y * F y) =
      p.mean (fun x => ind (bad x) * p.mean (fun y => a y * kernel x y)) := by
    intro a
    unfold F
    rw [mean_kernel]
    apply p.mean_congr; intro x
    rw [← mean_scale]
    exact p.mean_congr (fun _ => by ring)
  have h₁ : u * p.prob bad ≤ p.mean (fun y => ind (e y) * F y) := by
    rw [aux]; exact p.restricted_ge lower
  have h₂ : p.mean (fun y => F y * F y) ≤ C * p.prob bad := by
    rw [aux]
    apply p.restricted_le
    intro x hx
    simp_rw [mul_comm (F _) (kernel _ _)]
    rw [aux]
    exact upper x hx
  have hb := p.mean_mono (fun y => show 2*u*C*(ind (e y)*F y) ≤ u^2*(F y*F y) + C^2*ind (e y) by
    by_cases he : e y <;> simp only [ind,he,↓reduceIte] <;> nlinarith [sq_nonneg (u*F y-C),sq_nonneg (u*F y)])
  rw [mean_scale,mean_add,mean_scale,mean_scale,mean_ind] at hb
  apply le_of_mul_le_mul_left _ hc
  linarith [mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*u*C by positivity),
    mul_le_mul_of_nonneg_left h₂ (sq_nonneg u)]

end OAI.Geometry.Hirsch.Layer.Law
end

-- Pins
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω] [DecidableEq I]

structure Pins (p : Law Ω) (I : Type) where
  rate : ℝ
  pos : 0 < rate
  success : Ω → Finset I
  prob : ∀ s : Finset I, p.prob (fun x => s ⊆ success x) = rate^s.card

namespace Pins

open Law

variable {p : Law Ω} (pins : Pins p I)

def weight (s : Finset I) := pins.rate^s.card

omit [DecidableEq I] in
theorem positive (s : Finset I) : 0 < pins.weight s := pow_pos pins.pos _

theorem weight_union {s t : Finset I} (hd : Disjoint s t) :
    pins.weight (s ∪ t) = pins.weight s * pins.weight t := by
  simp [weight,Finset.card_union_of_disjoint hd,pow_add]

theorem weight_inter (s t : Finset I) :
    pins.weight (s ∪ t) * pins.weight (s ∩ t) = pins.weight s * pins.weight t := by
  simp [weight,← pow_add,Finset.card_union_add_card_inter]

def joint (e : Ω → Prop) (s : Finset I) := p.prob (fun x => e x ∧ s ⊆ pins.success x)

def given (e : Ω → Prop) (s : Finset I) := pins.joint e s / pins.weight s

def density (s : Finset I) (x : Ω) := (pins.weight s)⁻¹ * ind (s ⊆ pins.success x)

omit [DecidableEq I] in
theorem resolve (e : Ω → Prop) (s : Finset I) :
    p.mean (fun x => ind (e x) * pins.density s x) = pins.given e s := by
  simp_rw [density,mul_left_comm (ind _) (pins.weight s)⁻¹,ind_mul]
  rw [mean_scale,mean_ind,inv_mul_eq_div]; rfl

theorem overlap (s t : Finset I) : p.mean (fun x => pins.density s x * pins.density t x) =
    (pins.weight (s ∩ t))⁻¹ := by
  have he : ∀ x, pins.density s x * pins.density t x =
      (pins.weight s * pins.weight t)⁻¹ * ind (s ∪ t ⊆ pins.success x) := by
    intro x
    simp only [density,Finset.union_subset_iff,← ind_mul,mul_inv_rev]
    ring
  rw [p.mean_congr he,mean_scale,mean_ind,pins.prob,← pins.weight_inter]
  change (_ * _)⁻¹ * pins.weight (s ∪ t) = _
  rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pins.positive _).ne',mul_one]

theorem cross {P S : Finset I} (sub : S ⊆ P) {bad : Ω → Prop} {more : Ω → Finset I}
    (present : ∀ x, bad x → P ∪ more x ⊆ pins.success x) {R : Finset I} (hr : Disjoint P R) :
    p.mean (fun z => ind (bad z) * p.mean (fun y =>
      pins.density (S ∪ R) y * pins.density (S ∪ more z) y)) ≤
        (2 : ℝ)^R.card * (pins.weight P / pins.weight S) := by
  let f := fun J z => (pins.weight (S ∪ J))⁻¹ * ind (P ∪ J ⊆ pins.success z)
  have hn : ∀ J z, 0 ≤ f J z := fun J z => mul_nonneg (inv_nonneg.mpr (pins.positive _).le) (ind_nonneg _)
  have bound : ∀ z, ind (bad z) * p.mean (fun y =>
      pins.density (S ∪ R) y * pins.density (S ∪ more z) y) ≤ ∑ J ∈ R.powerset, f J z := by
    intro z
    by_cases hz : bad z
    swap
    · simp only [ind,hz,↓reduceIte,zero_mul]
      exact Finset.sum_nonneg (fun J _ => hn J z)
    let J := R ∩ more z
    have he : (S ∪ R) ∩ (S ∪ more z) = S ∪ J := by ext; simp [J]; tauto
    have hj : P ∪ J ⊆ pins.success z :=
      (Finset.union_subset_union_right Finset.inter_subset_right).trans (present z hz)
    have hmem : J ∈ R.powerset := Finset.mem_powerset.mpr Finset.inter_subset_left
    apply le_trans _ (Finset.single_le_sum (fun j _ => hn j z) hmem)
    rw [pins.overlap,he]
    simp [f,ind,hz,hj]
  have value : ∀ J ∈ R.powerset, p.mean (f J) = pins.weight P / pins.weight S := by
    intro J hJ
    have hd := hr.mono_right (Finset.mem_powerset.mp hJ)
    simp only [f,mean_scale,mean_ind,pins.prob]
    change (pins.weight (S ∪ J))⁻¹ * pins.weight (P ∪ J) = _
    rw [pins.weight_union hd,pins.weight_union (hd.mono_left sub),inv_mul_eq_div,
      mul_div_mul_right _ _ (pins.positive J).ne']
  apply (p.mean_mono bound).trans_eq
  rw [mean_sum,Finset.sum_congr rfl value]
  simp

theorem conditional_tail {P S : Finset I} (sub : S ⊆ P) (e : Ω → Prop) (K : ℕ) {u : ℝ} (hu : 0 < u) :
    u^2 * pins.given (fun x => ∃ R : Finset I, Disjoint P R ∧ R.card ≤ K ∧ R ⊆ pins.success x ∧
      u ≤ pins.given e (S ∪ R)) P ≤ (2 : ℝ)^K * pins.given e S := by
  let success := fun x (R : Finset I) => Disjoint P R ∧ R.card ≤ K ∧ R ⊆ pins.success x ∧
    u ≤ pins.given e (S ∪ R)
  let bad := fun x => (∃ R, success x R) ∧ P ⊆ pins.success x
  have hex : ∀ x, ∃ R, bad x → success x R := by
    intro x
    by_cases hx : bad x
    · obtain ⟨R,hR⟩ := hx.1; exact ⟨R,fun _ => hR⟩
    · exact ⟨∅,fun h => (hx h).elim⟩
  choose R hR using hex
  let C := (2 : ℝ)^K * (pins.weight P / pins.weight S)
  have hr := div_pos (pins.positive P) (pins.positive S)
  have hc : 0 < C := mul_pos (by positivity) hr
  have test := p.transfer bad (fun y => e y ∧ S ⊆ pins.success y)
    (fun x => pins.density (S ∪ R x)) hu hc
  have h : u^2 * p.prob bad ≤ C * pins.joint e S := by
    apply test
    · intro x hx
      apply (hR _ hx).2.2.2.trans_eq
      rw [← pins.resolve]
      apply p.mean_congr
      intro y
      by_cases hy : S ⊆ pins.success y
      · simp [hy]
      · simp [density,ind,Finset.union_subset_iff,hy]
    · intro x hx
      apply (pins.cross sub (fun z hz => Finset.union_subset hz.2 (hR z hz).2.2.1) (hR x hx).1).trans
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (hR x hx).2.1) hr.le
  change u^2 * (p.prob bad / pins.weight P) ≤ (2 : ℝ)^K * (pins.joint e S / pins.weight S)
  rw [← mul_div_assoc,div_le_iff₀ (pins.positive P)]
  exact h.trans_eq (by unfold C; ring)

end Pins
end OAI.Geometry.Hirsch.Layer
end

-- Screens
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω]

theorem Law.either (p : Law Ω) (e f : Ω → Prop) :
    p.prob (fun x => e x ∨ f x) ≤ p.prob e + p.prob f := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : e x <;> by_cases hf : f x <;> simp [he,hf,p.nonneg]

structure Thresholds (K : ℕ) where
  value : ℕ → ℝ
  positive : ∀ j, 0 < value j
  mono : Monotone value
  ratio : ∀ j < K, value j ≤ value (j+1)^2 * value K

namespace Pins

open Law

variable {p : Law Ω} (pins : Pins p I)

def cond (s : Finset I) : Law Ω where
  mass x := p.mass x * pins.density s x
  nonneg x := mul_nonneg (p.nonneg x) (mul_nonneg (inv_nonneg.mpr (pins.positive _).le) (ind_nonneg _))
  total := by
    change p.mean (pins.density s) = 1
    unfold density
    rw [mean_scale,mean_ind,pins.prob]
    exact inv_mul_cancel₀ (pins.positive s).ne'

@[simp] theorem cond_prob (e : Ω → Prop) (s : Finset I) : (pins.cond s).prob e = pins.given e s := by
  rw [← resolve,← mean_ind]
  unfold mean
  exact Finset.sum_congr rfl fun _ _ => by dsimp only [cond]; ring

variable {K : ℕ} (thr : Thresholds K) (e : Ω → Prop)

def Compatible (P : Finset I) : Prop :=
  ∀ S ⊆ P, S.card ≤ K → pins.given e S ≤ thr.value S.card

def Screen (x : Ω) : Prop := ¬e x ∧ pins.Compatible thr e (pins.success x)

theorem passes {x : Ω} (hs : pins.Screen thr e x) {P : Finset I} (hp : P ⊆ pins.success x) :
    pins.Compatible thr e P := fun _ hh => hs.2 _ (hh.trans hp)

theorem screen_cost {P : Finset I} (hk : P.card ≤ K) (hp : pins.Compatible thr e P) :
    pins.given (fun x => ¬pins.Screen thr e x) P ≤ (1 + (4 : ℝ)^K) * thr.value K := by
  let T := ↥P.powerset
  let bad := fun (S : T) (x : Ω) => S.val.card < K ∧ ∃ R : Finset I, Disjoint P R ∧ R.card ≤ K ∧
    R ⊆ pins.success x ∧ thr.value (S.val.card+1) ≤ pins.given e (S.val ∪ R)
  let q := pins.cond P
  have bound : ∀ S, q.prob (bad S) ≤ (2 : ℝ)^K * thr.value K := by
    intro S
    have hsub := Finset.mem_powerset.mp S.property
    by_cases hs : S.val.card < K
    swap
    · simp [bad,hs,Law.prob,(thr.positive K).le]
    let u := thr.value (S.val.card+1)
    have hu := thr.positive (S.val.card+1)
    apply le_of_mul_le_mul_left _ (sq_pos_of_pos hu)
    have hh := pins.conditional_tail hsub e K hu
    simp only [bad,hs,true_and,q,cond_prob]
    calc
      _ ≤ (2 : ℝ)^K * pins.given e S.val := hh
      _ ≤ (2 : ℝ)^K * (u^2 * thr.value K) := mul_le_mul_of_nonneg_left
        ((hp S.val hsub hs.le).trans (thr.ratio _ hs)) (by positivity)
      _ = _ := by unfold u; ring
  have cover : ∀ x, ¬pins.Screen thr e x → e x ∨ ∃ S, bad S x := by
    intro x hx
    by_cases he : e x
    · exact .inl he
    right
    have hn : ¬pins.Compatible thr e (pins.success x) := fun h => hx ⟨he,h⟩
    unfold Compatible at hn
    push Not at hn
    obtain ⟨J,hj,hk',hh⟩ := hn
    let S := J ∩ P
    have sub : S ⊆ P := Finset.inter_subset_right
    have proper : S ⊂ J := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_left,fun eq => hh.not_ge (hp J (eq ▸ sub) hk')⟩
    have hl := Finset.card_lt_card proper
    have join : S ∪ (J \ P) = J := by ext; simp [S]; tauto
    refine ⟨⟨S,Finset.mem_powerset.mpr sub⟩,hl.trans_le hk',J \ P,?_,
      (Finset.card_le_card Finset.sdiff_subset).trans hk',Finset.sdiff_subset.trans hj,?_⟩
    · exact Finset.disjoint_left.mpr fun _ h h' => (Finset.mem_sdiff.mp h').2 h
    · rw [join]
      exact (thr.mono hl).trans hh.le
  have hc : (Fintype.card T : ℝ) ≤ 2^K := by
    simp only [T,Fintype.card_coe,Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hk
  have cost : q.prob (fun x => ∃ S, bad S x) ≤ (4 : ℝ)^K * thr.value K := by
    calc
      _ ≤ ∑ S, q.prob (bad S) := q.union bad
      _ ≤ ∑ _ : T, (2 : ℝ)^K * thr.value K := Finset.sum_le_sum fun i _ => bound i
      _ ≤ 2^K * (2^K * thr.value K) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (thr.positive K).le)
      _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num
  have low : q.prob e ≤ thr.value K := by
    rw [show q = pins.cond P from rfl,cond_prob]
    exact (hp _ Finset.Subset.rfl hk).trans (thr.mono hk)
  rw [← cond_prob]
  exact (q.mono cover).trans ((q.either _ _).trans (by linarith))

end Pins
end OAI.Geometry.Hirsch.Layer
end

-- CutPaths
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Trial (I : Type) := Set (List I)

namespace Trial

variable {I Z : Type} (place : I → Z)

def Hit (s : Finset I) (path : List I) := ∃ g ∈ path, g ∈ s

def Covers (paths : Trial I) (s : Finset I) := ∀ path ∈ paths, Hit s path

def Minimal (paths : Trial I) (s : Finset I) := ∀ t ⊂ s, ¬paths.Covers t

def Refines (p q : Trial I) := ∀ s, q.Covers s → p.Covers s

def Transfers (short long : Trial I) (next : I → Trial I) :=
  ∀ pre g rest, pre ++ g :: rest ∈ short → ∀ s, long.Covers s → ¬Hit s pre → g ∉ s → (next g).Covers s

def keysAt (path : List I) (sites : Finset Z) := path.toFinset.filter (fun g => place g ∈ sites)

def Bounded (paths : Trial I) (e : ℕ) := ∀ path ∈ paths, ∀ j, (keysAt place path {j}).card ≤ e

variable {place} {s t : Finset I} {paths : Trial I} {path : List I}

theorem Hit.mono (hh : Hit s path) (hs : s ⊆ t) : Hit t path := by
  obtain ⟨g,hg,hm⟩ := hh
  exact ⟨g,hg,hs hm⟩

theorem Covers.mono (hc : paths.Covers s) (hs : s ⊆ t) : paths.Covers t := fun l hl => (hc l hl).mono hs

theorem Covers.nonempty (hc : paths.Covers s) (hn : paths.Nonempty) : s.Nonempty := by
  obtain ⟨l,hl⟩ := hn
  obtain ⟨g,_,hg⟩ := hc l hl
  exact ⟨g,hg⟩

theorem missed (hn : ¬paths.Covers s) : ∃ path ∈ paths, ¬Hit s path := by
  unfold Covers at hn
  push Not at hn
  exact hn

theorem Hit.first (hh : Hit s path) : ∃ pre g rest, path = pre ++ g :: rest ∧ ¬Hit s pre ∧ g ∈ s := by
  induction path with
  | nil => simp [Hit] at hh
  | cons g rest ih =>
    by_cases hg : g ∈ s
    · exact ⟨[],g,rest,rfl,by simp [Hit],hg⟩
    · have hr : Hit s rest := by simpa [Hit,hg] using hh
      obtain ⟨pre,j,tail,rfl,hn,hj⟩ := ih hr
      exact ⟨g :: pre,j,tail,rfl,by simpa [Hit,hg] using hn,hj⟩

theorem Minimal.essential (hm : paths.Minimal s) (hc : paths.Covers s) {g : I} (hg : g ∈ s) :
    ∃ pre rest, pre ++ g :: rest ∈ paths ∧ ¬ Hit s pre := by
  obtain ⟨path,hp,hn⟩ := missed (hm _ (Finset.erase_ssubset hg))
  obtain ⟨pre,j,rest,rfl,hpre,hj⟩ := (hc path hp).first
  have : j = g := by
    by_contra h
    exact hn ⟨j,by simp,Finset.mem_erase.mpr ⟨h,hj⟩⟩
  subst j
  exact ⟨pre,rest,hp,hpre⟩

@[simp] theorem mem_at {sites : Finset Z} {g : I} :
    g ∈ keysAt place path sites ↔ g ∈ path ∧ place g ∈ sites := by simp [keysAt]

theorem Bounded.sites {e : ℕ} (hb : paths.Bounded place e) (hp : path ∈ paths) (sites : Finset Z) :
    (keysAt place path sites).card ≤ sites.card * e := by
  induction sites using Finset.induction_on with
  | empty => simp [keysAt]
  | @insert j sites hj ih =>
    have he : keysAt place path (insert j sites) = keysAt place path sites ∪ keysAt place path {j} := by
      ext; simp; tauto
    rw [he,Finset.card_insert_of_notMem hj,add_mul,one_mul]
    exact (Finset.card_union_le ..).trans (Nat.add_le_add ih (hb _ hp _))

structure Tests (place : I → Z) (e d : ℕ) where
  short : Trial I
  long : Trial I
  next : I → Trial I
  refines : short.Refines long
  transfer : short.Transfers long next
  shortBound : short.Bounded place e
  nextBound : ∀ g, (next g).Bounded place d

namespace Tests

variable {e d : ℕ} (tests : Tests place e d)

def Available (a : Finset I) :=
  ∀ g ∈ a, ∃ path ∈ tests.next g, ∀ j ∈ path, j ∈ a → place j = place g

def Branches (a : Finset I) (K M : ℕ) :=
  ∀ s ⊆ a, s.card < K → ¬tests.short.Covers s →
    ∃ choices : Finset I, choices.card ≤ M ∧ ∀ t ⊆ a, s ⊆ t → tests.long.Covers t →
      ∃ g ∈ choices, g ∈ t ∧ g ∉ s

theorem branch {a : Finset I} (ha : tests.Available a) (K : ℕ) :
    tests.Branches a K (K*e+1+d) := by
  intro s hsa hK hmiss
  obtain ⟨path,hp,hn⟩ := missed hmiss
  let sites := s.image place
  let first := keysAt place path sites
  have hs : sites.card ≤ K := Finset.card_image_le.trans hK.le
  have hsize : first.card ≤ K*e := (tests.shortBound.sites hp sites).trans (Nat.mul_le_mul_right _ hs)
  have avoid : ∀ g ∈ path, g ∉ s := fun g hg hm => hn ⟨g,hg,hm⟩
  by_cases hh : Hit (a \ first) path
  swap
  · refine ⟨first,by omega,fun t ht _ hc => ?_⟩
    obtain ⟨g,hg,hg'⟩ := tests.refines _ hc _ hp
    exact ⟨g,by_contra (fun h => hh ⟨g,hg,Finset.mem_sdiff.mpr ⟨ht hg',h⟩⟩),hg',avoid g hg⟩
  obtain ⟨pre,g,rest,he,hpre,hg⟩ := hh.first
  have hp' : g ∈ path := by simp [he]
  obtain ⟨hga,hnf⟩ := Finset.mem_sdiff.mp hg
  have free : place g ∉ sites := fun h => hnf (mem_at.mpr ⟨hp',h⟩)
  obtain ⟨tail,ht,hallow⟩ := ha g hga
  let extra := keysAt place tail {place g}
  have hex : extra.card ≤ d := tests.nextBound g tail ht _
  refine ⟨insert g (first ∪ extra),?_,fun t hta _ hc => ?_⟩
  · have := Finset.card_insert_le g (first ∪ extra)
    have := Finset.card_union_le first extra
    omega
  by_cases hgf : ∃ j ∈ first, j ∈ t
  · obtain ⟨j,hj,hm⟩ := hgf
    exact ⟨j,by simp [hj],hm,avoid j (mem_at.mp hj).1⟩
  by_cases hgt : g ∈ t
  · exact ⟨g,by simp,hgt,avoid g hp'⟩
  have sub : t ⊆ a \ first := fun j hj => Finset.mem_sdiff.mpr ⟨hta hj,fun h => hgf ⟨j,h,hj⟩⟩
  obtain ⟨j,hj,hm⟩ := tests.transfer _ _ _ (he ▸ hp) t hc (fun h => hpre (h.mono sub)) hgt tail ht
  have hsite := hallow j hj (hta hm)
  have hj' : j ∈ extra := mem_at.mpr ⟨hj,Finset.mem_singleton.mpr hsite⟩
  refine ⟨j,by simp [hj'],hm,fun h => ?_⟩
  exact free (hsite ▸ Finset.mem_image_of_mem _ h)

end Tests
end Trial
end OAI.Geometry.Hirsch.Layer
end

-- CutSearch
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial.Tests

variable {I Z : Type} {place : I → Z} {e d K M : ℕ} {tests : Tests place e d} {a : Finset I}

def Frontier (tests : Tests place e d) (a : Finset I) (K : ℕ) (start : Finset I)
    (leaves : Finset (Finset I)) :=
  (∀ s ∈ leaves, (s ⊆ a ∧ s.card ≤ K) ∧ (s.card = K ∨ tests.short.Covers s)) ∧
    ∀ t ⊆ a, start ⊆ t → tests.long.Covers t → ∃ s ∈ leaves, s ⊆ t

theorem Branches.search (hb : tests.Branches a K M) (k : ℕ) (s : Finset I)
    (hs : s ⊆ a) (hk : s.card + k = K) :
    ∃ leaves, leaves.card ≤ (M+1)^k ∧ tests.Frontier a K s leaves := by
  induction k generalizing s with
  | zero =>
    refine ⟨{s},by simp,?_,fun t _ ht _ => ⟨s,by simp,ht⟩⟩
    simpa using (show (s ⊆ a ∧ s.card ≤ K) ∧ (s.card = K ∨ tests.short.Covers s) from ⟨⟨hs,by omega⟩,.inl (by omega)⟩)
  | succ k ih =>
    by_cases hc : tests.short.Covers s
    · refine ⟨{s},by simp only [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by omega),
        ?_,fun t _ ht _ => ⟨s,by simp,ht⟩⟩
      simp [hs,hc,show s.card ≤ K by omega]
    obtain ⟨choices,hm,hh⟩ := hb s hs (by omega) hc
    let opts := choices.filter (fun g => g ∈ a ∧ g ∉ s)
    have next : ∀ g : ↥opts, ∃ leaves, leaves.card ≤ (M+1)^k ∧ tests.Frontier a K (insert g.val s) leaves := by
      intro g
      obtain ⟨_,hin,hout⟩ := Finset.mem_filter.mp g.property
      apply ih _ (Finset.insert_subset hin hs)
      rw [Finset.card_insert_of_notMem hout]
      omega
    choose src hn hp using next
    refine ⟨Finset.univ.biUnion src,?_,?_,?_⟩
    · calc
        _ ≤ ∑ i, (src i).card := Finset.card_biUnion_le
        _ ≤ ∑ _ : ↥opts, (M+1)^k := Finset.sum_le_sum fun i _ => hn i
        _ ≤ (M+1)^(k+1) := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,pow_succ']
          apply Nat.mul_le_mul_right
          exact ((Finset.card_filter_le ..).trans hm).trans (by omega)
    · intro u hu
      obtain ⟨g,_,hu⟩ := Finset.mem_biUnion.mp hu
      exact (hp g).1 _ hu
    · intro t ht hst hl
      obtain ⟨g,hg,hgt,hgs⟩ := hh _ ht hst hl
      let opt : ↥opts := ⟨g,Finset.mem_filter.mpr ⟨hg,ht hgt,hgs⟩⟩
      obtain ⟨u,hu,hs⟩ := (hp opt).2 t ht (Finset.insert_subset hgt hst) hl
      exact ⟨u,Finset.mem_biUnion.mpr ⟨opt,Finset.mem_univ _,hu⟩,hs⟩

def capacity (K e d : ℕ) := (K*e+1+d+1)^K

theorem Available.frontier (ha : tests.Available a) (K : ℕ) :
    ∃ leaves, leaves.card ≤ capacity K e d ∧ tests.Frontier a K ∅ leaves :=
  (tests.branch ha K).search K ∅ (Finset.empty_subset _) (by simp)

def Listed (tests : Tests place e d) (K : ℕ) (s : Finset I) :=
  s.card ≤ K ∧ tests.long.Covers s ∧ tests.short.Minimal s

theorem Frontier.includes {leaves : Finset (Finset I)} (hf : tests.Frontier a K ∅ leaves)
    {s : Finset I} (hs : tests.Listed K s) (ha : s ⊆ a) : s ∈ leaves := by
  obtain ⟨t,ht,hsub⟩ := hf.2 s ha (Finset.empty_subset _) hs.2.1
  suffices t = s from this ▸ ht
  rcases (hf.1 t ht).2 with he | hc
  · exact Finset.eq_of_subset_of_card_le hsub (he ▸ hs.1)
  · exact by_contra (fun hn => hs.2.2 t (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hn⟩) hc)

theorem Available.multiplicity (ha : tests.Available a) {list : Finset (Finset I)}
    (hl : ∀ s ∈ list, tests.Listed K s ∧ s ⊆ a) : list.card ≤ capacity K e d := by
  obtain ⟨leaves,hc,hf⟩ := ha.frontier K
  exact (Finset.card_le_card fun s hs => hf.includes (hl _ hs).1 (hl _ hs).2).trans hc

end OAI.Geometry.Hirsch.Layer.Trial.Tests
end

-- CutMass
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I Z : Type} [Fintype Ω] {p : Law Ω}

namespace Law

theorem union_finset (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) :
    p.prob (fun x => ∃ i ∈ s, e i x) ≤ ∑ i ∈ s, p.prob (e i) := by
  have hh := p.union (fun i : ↥s => e i.val)
  rw [Finset.sum_coe_sort s (fun i => p.prob (e i))] at hh
  simpa only [Subtype.exists,exists_prop] using hh

theorem count (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) :
    ∑ i ∈ s, p.prob (e i) = p.mean (fun x => ((s.filter (fun i => e i x)).card : ℝ)) := by
  simp_rw [← mean_ind]
  rw [← mean_sum]
  apply p.mean_congr
  intro x
  simp [ind]

theorem multiplicity (p : Law Ω) (s : Finset I) (e : I → Ω → Prop) (event : Ω → Prop) {M : ℕ}
    (hb : ∀ x, (s.filter (fun i => e i x)).card ≤ M)
    (he : ∀ i ∈ s, ∀ x, e i x → event x) :
    ∑ i ∈ s, p.prob (e i) ≤ M * p.prob event := by
  rw [count,← mean_ind,← mean_scale]
  apply p.mean_mono
  intro x
  by_cases hx : event x
  · simpa [ind,hx] using hb x
  · have hzero : s.filter (fun i => e i x) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun i hi hh => hx (he i hi x hh))
    simp [ind,hx,hzero]

end Law

namespace Pins

variable (pins : Pins p I)

def mass (family : Finset (Finset I)) := ∑ s ∈ family, pins.weight s

theorem mass_nonneg (family : Finset (Finset I)) : 0 ≤ pins.mass family :=
  Finset.sum_nonneg fun _ _ => (pins.positive _).le

theorem mass_mono {a b : Finset (Finset I)} (h : a ⊆ b) : pins.mass a ≤ pins.mass b :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => (pins.positive _).le

theorem mass_split (s : Finset (Finset I)) (P : Finset I → Prop) [DecidablePred P] :
    pins.mass (s.filter P) + pins.mass (s.filter fun t => ¬P t) = pins.mass s :=
  Finset.sum_filter_add_sum_filter_not ..

theorem extra (s a : Finset I) (hn : ∀ i ∈ a, i ∉ s) :
    p.prob (fun x => s ⊆ pins.success x ∧ ∃ i ∈ a, i ∈ pins.success x) ≤
      a.card * pins.rate * pins.weight s := by
  calc
    _ ≤ p.prob (fun x => ∃ i ∈ a, insert i s ⊆ pins.success x) :=
      p.mono (fun _ ⟨hs,i,hi,hm⟩ => ⟨i,hi,Finset.insert_subset hm hs⟩)
    _ ≤ ∑ i ∈ a, p.prob (fun x => insert i s ⊆ pins.success x) := p.union_finset ..
    _ = ∑ _ ∈ a, pins.rate * pins.weight s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pins.prob,Finset.card_insert_of_notMem (hn i hi),pow_succ']
      rfl
    _ = _ := by simp [mul_assoc]

end Pins

namespace Trial

variable {place : I → Z} {K e d : ℕ} {tests : Tests place e d}

structure Gates (pins : Pins p I) (place : I → Z) (K : ℕ) (gamma alpha : ℝ) where
  pass : Ω → Finset I
  pinned : ∀ x, pass x ⊆ pins.success x
  bad : I → Ω → Prop
  screen : ∀ x g, g ∈ pass x → ¬bad g x
  possible : ∀ s : Finset I, s.card ≤ K → (∃ x, s ⊆ pass x) →
    gamma * pins.weight s ≤ p.prob (fun x => s ⊆ pass x)
  compatible : ∀ x g, g ∈ pass x → ∀ s ⊆ pass x, s.card ≤ K → pins.given (bad g) s ≤ alpha

namespace Gates

variable {pins : Pins p I} {gamma alpha : ℝ} (gate : Gates pins place K gamma alpha)

def Serves (tests : Tests place e d) :=
  ∀ x g, ¬gate.bad g x → ∃ path ∈ tests.next g, ∀ j ∈ path, j ∈ gate.pass x → place j = place g

theorem Serves.available {gate : Gates pins place K gamma alpha} (hs : gate.Serves tests) (x : Ω) :
    tests.Available (gate.pass x) := fun g hg => hs x g (gate.screen _ _ hg)

def ListAt (tests : Tests place e d) (family : Finset (Finset I)) :=
  ∀ s ∈ family, tests.Listed K s ∧ ∃ x, s ⊆ gate.pass x

variable {gate} {family : Finset (Finset I)}

theorem ListAt.sub {sub : Finset (Finset I)} (hl : gate.ListAt tests family) (hs : sub ⊆ family) :
    gate.ListAt tests sub := fun s hh => hl s (hs hh)

theorem ListAt.estimate {Γ : Type} [Fintype Γ] (hl : gate.ListAt tests family) (hs : gate.Serves tests)
    (q : Law Γ) (original : Γ → Ω) (hit : Finset I → Γ → Prop) (event : Γ → Prop)
    (lower : ∀ s ∈ family, gamma * pins.weight s ≤ q.prob (hit s))
    (pass : ∀ s ∈ family, ∀ x, hit s x → s ⊆ gate.pass (original x))
    (implies : ∀ s ∈ family, ∀ x, hit s x → event x) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * q.prob event := by
  rw [Pins.mass,Finset.mul_sum]
  apply (Finset.sum_le_sum lower).trans
  apply q.multiplicity _ _ _ _ implies
  intro x
  apply (hs.available (original x)).multiplicity
  intro s hh
  obtain ⟨hf,hx⟩ := Finset.mem_filter.mp hh
  exact ⟨(hl _ hf).1,pass s hf x hx⟩

theorem ListAt.bound (hl : gate.ListAt tests family) (hs : gate.Serves tests) (event : Ω → Prop)
    (implies : ∀ s ∈ family, ∀ x, s ⊆ gate.pass x → event x) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * p.prob event :=
  hl.estimate hs p id (fun s x => s ⊆ gate.pass x) event
    (fun s hf => gate.possible _ (hl s hf).1.1 (hl s hf).2) (fun _ _ _ h => h) implies

end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
end

-- CutLinks
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial.Gates

variable {Ω I Z : Type} [Fintype Ω] {p : Law Ω} {place : I → Z} {K e d : ℕ}
  {tests : Tests place e d} {pins : Pins p I} {gamma alpha : ℝ}

structure Resample (gate : Gates pins place K gamma alpha) (site : Z) where
  Resp : Type
  [finite : Fintype Resp]
  law : Law Resp
  before : Resp → Ω
  after : Resp → Ω
  marginal : ∀ E, law.prob (fun x => E (after x)) = p.prob E
  fixed : ∀ x g, place g ≠ site → (g ∈ pins.success (before x) ↔ g ∈ pins.success (after x))
  extra : ∀ (s : Finset I) (f : Ω → Finset I) (N : ℕ), site ∉ s.image place →
    (∀ x, (f x).card ≤ N ∧ ∀ i ∈ f x, place i = site) →
    law.prob (fun x => s ⊆ pins.success (before x) ∧ ∃ i ∈ f (after x), i ∈ pins.success (before x)) ≤
      N * pins.rate * pins.weight s
  possible : ∀ s : Finset I, s.card ≤ K → (∃ x, s ⊆ gate.pass x) →
    gamma * pins.weight s ≤ law.prob (fun x => s ⊆ gate.pass (before x) ∧
      ∀ i ∈ s, place i ≠ site → i ∈ gate.pass (after x))

local instance respFinite {gate : Gates pins place K gamma alpha} {site : Z} (r : gate.Resample site) : Fintype r.Resp := r.finite

variable {gate : Gates pins place K gamma alpha} {family : Finset (Finset I)}
  (hl : gate.ListAt tests family) (hs : gate.Serves tests) (s : Finset I)

include hl hs in
theorem ListAt.foreign {g : I} (change : gate.Resample (place g))
    (fresh : place g ∉ s.image place) (contains : ∀ t ∈ family, s ⊆ t)
    (some : ∃ t ∈ family, g ∈ t) (transfer : ∀ t ∈ family, g ∉ t → (tests.next g).Covers t) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * (alpha + (d+1)*pins.rate) * pins.weight s := by
  have hex : ∀ x, ∃ f : Finset I, (f.card ≤ d+1 ∧ ∀ i ∈ f, place i = place g) ∧
      (¬gate.bad g x → ∀ t ∈ family, (∀ i ∈ t, place i ≠ place g → i ∈ gate.pass x) →
        ∃ i ∈ f, i ∈ t) := by
    intro x
    by_cases hb : gate.bad g x
    · exact ⟨∅,by simp,fun h => (h hb).elim⟩
    obtain ⟨path,hp,hh⟩ := hs x g hb
    refine ⟨insert g (keysAt place path {place g}),⟨?_,?_⟩,fun _ t ht hpass => ?_⟩
    · exact (Finset.card_insert_le ..).trans (Nat.add_le_add_right (tests.nextBound g _ hp _) 1)
    · simp
    · by_cases hg : g ∈ t
      · exact ⟨g,by simp,hg⟩
      obtain ⟨i,hi,hit⟩ := transfer t ht hg path hp
      have eq : place i = place g := by_contra fun hn => hn (hh i hi (hpass i hit hn))
      exact ⟨i,by simp [hi,eq],hit⟩
  choose f hsize hf using hex
  let A := fun x => gate.bad g (change.after x) ∧ s ⊆ pins.success (change.after x)
  let B := fun x => s ⊆ pins.success (change.before x) ∧ ∃ i ∈ f (change.after x), i ∈ pins.success (change.before x)
  have ha : change.law.prob A ≤ alpha * pins.weight s := by
    obtain ⟨t,ht,hgt⟩ := some
    obtain ⟨⟨hk,_,_⟩,x,hx⟩ := hl _ ht
    have hc := gate.compatible x g (hx hgt) s ((contains _ ht).trans hx)
      ((Finset.card_le_card (contains _ ht)).trans hk)
    have he : change.law.prob A = pins.joint (gate.bad g) s :=
      change.marginal (fun x => gate.bad g x ∧ s ⊆ pins.success x)
    rw [he]
    exact (div_le_iff₀ (pins.positive s)).mp hc
  have hb : change.law.prob B ≤ (d+1)*pins.rate*pins.weight s := by
    simpa only [Nat.cast_add,Nat.cast_one] using change.extra s f (d+1) fresh hsize
  let hit := fun (t : Finset I) x => t ⊆ gate.pass (change.before x) ∧
    ∀ i ∈ t, place i ≠ place g → i ∈ gate.pass (change.after x)
  have key : gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) * change.law.prob (fun x => A x ∨ B x) := by
    apply hl.estimate hs change.law change.before hit _
      (fun t ht => change.possible t (hl _ ht).1.1 (hl _ ht).2) (fun _ _ _ hh => hh.1)
    intro t ht x hh
    have pin := hh.1.trans (gate.pinned _)
    have fixed := (contains _ ht).trans pin
    by_cases bad : gate.bad g (change.after x)
    · left
      refine ⟨bad,fun i hi => (change.fixed _ _ ?_).mp (fixed hi)⟩
      exact fun he => fresh (Finset.mem_image.mpr ⟨i,hi,he⟩)
    · obtain ⟨i,hi,hmem⟩ := hf _ bad t ht hh.2
      exact .inr ⟨fixed,i,hi,pin hmem⟩
  rw [mul_assoc]
  exact key.trans (mul_le_mul_of_nonneg_left ((change.law.either A B).trans (by linarith)) (by positivity))

include hl hs in
theorem ListAt.link (change : ∀ z, Nonempty (gate.Resample z)) (ha : 0 ≤ alpha)
    (contains : ∀ t ∈ family, s ⊂ t) :
    gamma * pins.mass family ≤ (Tests.capacity K e d : ℝ) *
      (alpha + (K*e+d+1)*pins.rate) * pins.weight s := by
  have hp := pins.pos
  have hw := pins.positive s
  by_cases hn : family.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp only [Pins.mass,Finset.sum_empty,mul_zero]
    positivity
  obtain ⟨t,ht⟩ := hn
  have hk := (Finset.card_lt_card (contains _ ht)).trans_le (hl _ ht).1.1
  obtain ⟨path,hpath,hmiss⟩ := missed ((hl _ ht).1.2.2 _ (contains _ ht))
  let a := keysAt place path (s.image place)
  have hsize : a.card ≤ K*e := (tests.shortBound.sites hpath _).trans
    (Nat.mul_le_mul_right _ (Finset.card_image_le.trans hk.le))
  let P := fun t : Finset I => ∃ i ∈ a, i ∈ t
  let left := family.filter P
  let right := family.filter (fun t => ¬P t)
  have hl₁ : gate.ListAt tests left := hl.sub (Finset.filter_subset ..)
  have hl₂ : gate.ListAt tests right := hl.sub (Finset.filter_subset ..)
  have h₁ : gamma * pins.mass left ≤ (Tests.capacity K e d : ℝ) * (K*e*pins.rate*pins.weight s) := by
    let E := fun x => s ⊆ pins.success x ∧ ∃ i ∈ a, i ∈ pins.success x
    have hh : gamma * pins.mass left ≤ (Tests.capacity K e d : ℝ) * p.prob E := by
      apply hl₁.bound hs
      intro t ht x hx
      obtain ⟨ht,i,hi,hm⟩ := Finset.mem_filter.mp ht
      exact ⟨(contains _ ht).subset.trans (hx.trans (gate.pinned _)),i,hi,gate.pinned _ (hx hm)⟩
    apply hh.trans
    gcongr
    apply (pins.extra s a (fun i hi hm => hmiss ⟨i,(mem_at.mp hi).1,hm⟩)).trans
    gcongr
    exact_mod_cast hsize
  have h₂ : gamma * pins.mass right ≤ (Tests.capacity K e d : ℝ) * (alpha+(d+1)*pins.rate)*pins.weight s := by
    by_cases hn : right.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simp only [Pins.mass,Finset.sum_empty,mul_zero]
      positivity
    let pool := right.biUnion id
    have incl : ∀ t ∈ right, t ⊆ pool := fun t ht _ hi => Finset.mem_biUnion.mpr ⟨t,ht,hi⟩
    obtain ⟨u,hu⟩ := hn
    obtain ⟨pre,g,rest,he,hpre,hg⟩ := ((tests.refines _ (hl₂ _ hu).1.2.1 _ hpath).mono (incl u hu)).first
    obtain ⟨v,hv,hg⟩ := Finset.mem_biUnion.mp hg
    have fresh : place g ∉ s.image place := fun h =>
      (Finset.mem_filter.mp hv).2 ⟨g,mem_at.mpr ⟨by simp [he],h⟩,hg⟩
    exact hl₂.foreign hs s (Classical.choice (change _)) fresh
      (fun t ht => (contains _ (Finset.mem_filter.mp ht).1).subset) ⟨v,hv,hg⟩
      (fun t ht hn => tests.transfer _ _ _ (he ▸ hpath) t (hl₂ _ ht).1.2.1
        (fun h => hpre (h.mono (incl t ht))) hn)
  rw [← pins.mass_split family P,mul_add]
  exact (add_le_add h₁ h₂).trans_eq (by ring)

end OAI.Geometry.Hirsch.Layer.Trial.Gates
end

-- CutLoss
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I J : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)

namespace Pins

theorem mass_cover (src : Finset (Finset I)) (indices : Finset J) (sets : J → Finset (Finset I))
    (covered : ∀ s ∈ src, ∃ j ∈ indices, s ∈ sets j) :
    pins.mass src ≤ ∑ j ∈ indices, pins.mass (sets j) := by
  calc
    _ ≤ ∑ s ∈ src, ∑ j ∈ indices, if s ∈ sets j then pins.weight s else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨j,hj,hm⟩ := covered s hs
      let f := fun i => if s ∈ sets i then pins.weight s else 0
      have hn : ∀ i ∈ indices, 0 ≤ f i := fun _ _ => by unfold f; split <;> simp [(pins.positive s).le]
      simpa [f,hm] using Finset.single_le_sum hn hj
    _ ≤ _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro j _
      rw [← Finset.sum_filter]
      exact pins.mass_mono (fun _ h => (Finset.mem_filter.mp h).2)

theorem mass_union (a b : Finset (Finset I)) : pins.mass (a ∪ b) ≤ pins.mass a + pins.mass b := by
  have he := Finset.sum_union_inter (s₁ := a) (s₂ := b) (f := pins.weight)
  exact (le_add_of_nonneg_right (pins.mass_nonneg (a ∩ b))).trans_eq he

end Pins

namespace Trial

theorem plateau (paths : ℕ → Trial I) {s : Finset I} {k : ℕ} (hk : s.card ≤ k)
    (hc : (paths (k+1)).Covers s) :
    ∃ j ≤ k, ∃ t ⊆ s, (paths (j+1)).Covers t ∧ (paths j).Minimal t := by
  induction k generalizing s with
  | zero =>
    refine ⟨0,le_rfl,s,Finset.Subset.rfl,hc,fun u hu => ?_⟩
    have := Finset.card_lt_card hu
    omega
  | succ k ih =>
    by_cases hm : (paths (k+1)).Minimal s
    · exact ⟨k+1,le_rfl,s,Finset.Subset.rfl,hc,hm⟩
    unfold Minimal at hm
    push Not at hm
    obtain ⟨u,hu,huc⟩ := hm
    obtain ⟨j,hj,t,ht,hc,hm⟩ := ih (by have := Finset.card_lt_card hu; omega) huc
    exact ⟨j,by omega,t,ht.trans hu.subset,hc,hm⟩

variable {pins} {Z : Type} {place : I → Z} {K e d : ℕ} {gamma alpha : ℝ}

namespace Gates

variable (gate : Gates pins place K gamma alpha)

def Possible (s : Finset I) := ∃ x, s ⊆ gate.pass x

def cuts [Fintype I] (short long : Trial I) :=
  Finset.univ.filter fun s : Finset I => s.card ≤ K ∧ long.Covers s ∧ short.Minimal s ∧ gate.Possible s

@[simp] theorem mem_cuts [Fintype I] {short long : Trial I} {s : Finset I} :
    s ∈ gate.cuts short long ↔ s.card ≤ K ∧ long.Covers s ∧ short.Minimal s ∧ gate.Possible s := by
  simp [cuts]

theorem listed [Fintype I] (tests : Tests place e d) :
    gate.ListAt tests (gate.cuts tests.short tests.long) := by
  intro s hs
  obtain ⟨hk,hc,hm,hp⟩ := gate.mem_cuts.mp hs
  exact ⟨⟨hk,hc,hm⟩,hp⟩

structure Bounds (family : Finset (Finset I)) (M A : ℝ) : Prop where
  mass : pins.mass family ≤ M
  possible : ∀ s ∈ family, s.card ≤ K ∧ gate.Possible s
  link : ∀ s, pins.mass (family.filter (s ⊂ ·)) ≤ A*pins.weight s

variable {gate} {M A : ℝ} {family : Finset (Finset I)}

theorem bounds [Fintype I] {tests : Tests place e d} (hs : gate.Serves tests)
    (hg : 0 < gamma) (ha : 0 ≤ alpha) (change : ∀ z, Nonempty (gate.Resample z))
    {U : ℝ} (cap : p.prob (fun x => tests.long.Covers (gate.pass x)) ≤ U)
    (hM : (Tests.capacity K e d : ℝ)*U ≤ gamma*M)
    (hA : (Tests.capacity K e d : ℝ)*(alpha+(K*e+d+1)*pins.rate) ≤ gamma*A) :
    gate.Bounds (gate.cuts tests.short tests.long) M A := by
  have hl := gate.listed tests
  refine ⟨?_,fun s hh => ⟨(hl s hh).1.1,(hl s hh).2⟩,fun s => ?_⟩
  · apply le_of_mul_le_mul_left _ hg
    exact (hl.bound hs _ (fun t ht _ hx => (hl t ht).1.2.1.mono hx)).trans
      ((mul_le_mul_of_nonneg_left cap (by positivity)).trans hM)
  · apply le_of_mul_le_mul_left _ hg
    rw [← mul_assoc]
    apply le_trans _ (mul_le_mul_of_nonneg_right hA (pins.positive s).le)
    exact (hl.sub (Finset.filter_subset ..)).link hs s change ha (fun _ hh => (Finset.mem_filter.mp hh).2)

theorem Bounds.key (hb : gate.Bounds family M A) (g : I) :
    pins.mass (family.filter (g ∈ ·)) ≤ (1+A)*pins.rate := by
  let one : Finset I := {g}
  have hsub : family.filter (g ∈ ·) ⊆ {one} ∪ family.filter (one ⊂ ·) := by
    intro t ht
    obtain ⟨ht,hg⟩ := Finset.mem_filter.mp ht
    by_cases he : t = one
    · simp [he]
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨ht,Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hg,Ne.symm he⟩⟩)
  apply (pins.mass_mono hsub).trans
  apply (pins.mass_union ..).trans
  have hh := hb.link one
  have he : pins.weight one = pins.rate := by simp [one,Pins.weight]
  rw [he] at hh
  have : pins.mass {one} = pins.rate := by simp [Pins.mass,he]
  linarith

theorem Bounds.loss [Fintype I] (hb : gate.Bounds family M A) (ha : 0 ≤ A) (paths : ℕ → Trial I)
    (bound : ∀ j ≤ K, pins.mass (gate.cuts (paths j) (paths (j+1))) ≤ M) :
    pins.mass (family.filter fun s => ¬(paths (K+1)).Minimal s) ≤ (K+1)*A*M := by
  let cuts := fun j => gate.cuts (paths j) (paths (j+1))
  let hits := fun j => family.filter fun s => ∃ t ∈ cuts j, t ⊂ s
  have one : ∀ j ≤ K, pins.mass (hits j) ≤ A*M := by
    intro j hj
    calc
      _ ≤ ∑ t ∈ cuts j, pins.mass (family.filter (t ⊂ ·)) := by
        apply pins.mass_cover
        intro s hs
        obtain ⟨hs,t,ht,hts⟩ := Finset.mem_filter.mp hs
        exact ⟨t,ht,Finset.mem_filter.mpr ⟨hs,hts⟩⟩
      _ ≤ ∑ t ∈ cuts j, A*pins.weight t := Finset.sum_le_sum fun t _ => hb.link t
      _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (bound j hj) ha
  calc
    _ ≤ ∑ j ∈ Finset.range (K+1), pins.mass (hits j) := by
      apply pins.mass_cover
      intro s hs
      obtain ⟨hs,hm⟩ := Finset.mem_filter.mp hs
      obtain ⟨hk,x,hx⟩ := hb.possible _ hs
      unfold Minimal at hm
      push Not at hm
      obtain ⟨u,hu,hc⟩ := hm
      obtain ⟨j,hj,t,ht,hc,hm⟩ := plateau paths ((Finset.card_le_card hu.subset).trans hk) hc
      have hts : t ⊂ s := lt_of_le_of_lt ht hu
      exact ⟨j,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨hs,t,gate.mem_cuts.mpr
        ⟨(Finset.card_le_card hts.subset).trans hk,hc,hm,x,hts.subset.trans hx⟩,hts⟩⟩
    _ ≤ ∑ _ ∈ Finset.range (K+1), A*M :=
      Finset.sum_le_sum fun j hj => one j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = _ := by simp [mul_assoc]

end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
end

-- CutOrder
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Trial

variable {I : Type} {s t : Finset I}

theorem Hit.append_left {p q : List I} (hh : Hit s p) : Hit s (p ++ q) := by
  obtain ⟨g,hg,hm⟩ := hh
  exact ⟨g,List.mem_append_left _ hg,hm⟩

def Before (paths : Trial I) (s t : Finset I) :=
  ∀ pre g rest, pre ++ g :: rest ∈ paths → g ∈ t → Hit s pre

theorem Before.missed {paths : Trial I} (hb : paths.Before s t) {pre tail : List I}
    (hh : pre ++ tail ∈ paths) (hn : ¬Hit s pre) : ¬Hit t pre := by
  intro hit
  obtain ⟨a,g,b,rfl,_,hg⟩ := hit.first
  exact hn (hb a g (b ++ tail) (by simpa using hh) hg).append_left

def Falls (rank : I → ℕ) (next : I → Trial I) :=
  ∀ g path, path ∈ next g → ∀ j ∈ path, rank j < rank g

theorem Falls.older {rank : I → ℕ} {next : I → Trial I} (hf : Falls rank next) {g : I}
    (hc : (next g).Covers s) (hm : (next g).Minimal s) : ∀ j ∈ s, rank j < rank g := by
  intro j hj
  obtain ⟨pre,rest,hp,_⟩ := hm.essential hc hj
  exact hf _ _ hp j (by simp)

structure Core (rank : I → ℕ) where
  short : Trial I
  long : Trial I
  paths : Trial I
  near : I → Trial I
  far : I → Trial I
  inhabited : short.Nonempty
  includes : short ⊆ paths
  refines : short.Refines long
  transfer : paths.Transfers long far
  nested : ∀ g, (near g).Refines (far g)
  falls : Falls rank near

namespace Core

variable {rank : I → ℕ} (core : Core rank)

def Cut (s : Finset I) := core.long.Covers s ∧ core.short.Minimal s

def Good (s t : Finset I) :=
  Disjoint s t ∧ (∀ g ∈ s, (core.near g).Minimal t) ∧ (∀ g ∈ t, (core.near g).Minimal s)

def Newer (s t : Finset I) := core.Good s t ∧ core.paths.Before s t ∧
  ∀ g ∈ s, (core.far g).Covers t ∧ ∀ j ∈ t, rank j < rank g

variable {core}

theorem Good.symm (hg : core.Good s t) : core.Good t s := ⟨hg.1.symm,hg.2.2,hg.2.1⟩

theorem Good.at_key (hg : core.Good s t) (ht : core.Cut t) {pre rest : List I} {g : I}
    (hp : pre ++ g :: rest ∈ core.paths) (hm : g ∈ s) (hn : ¬Hit t pre) :
    (core.far g).Covers t ∧ ∀ j ∈ t, rank j < rank g := by
  have hc := core.transfer _ _ _ hp _ ht.1 hn (Finset.disjoint_left.mp hg.1 hm)
  exact ⟨hc,core.falls.older (core.nested g _ hc) (hg.2.1 g hm)⟩

theorem Good.newer (hg : core.Good s t) (hs : core.Cut s) (ht : core.Cut t)
    (hn : ¬core.paths.Before t s) : core.Newer s t := by
  unfold Before at hn
  push Not at hn
  obtain ⟨pre,g,rest,hp,hm,hn⟩ := hn
  have hb := (hg.at_key ht hp hm hn).2
  have first : core.paths.Before s t := by
    intro a j b hh hj
    by_contra hmiss
    exact (hb j hj).not_gt ((hg.symm.at_key hs hh hj hmiss).2 g hm)
  refine ⟨hg,first,fun j hj => ?_⟩
  obtain ⟨a,b,hh,hmiss⟩ := hs.2.essential (core.refines _ hs.1) hj
  have hf := core.includes hh
  exact hg.at_key ht hf hj (first.missed hf hmiss)

theorem Good.order (hg : core.Good s t) (hs : core.Cut s) (ht : core.Cut t) :
    core.Newer s t ∨ core.Newer t s := by
  by_cases hf : core.paths.Before t s
  swap
  · exact .inl (hg.newer hs ht hf)
  right
  apply hg.symm.newer ht hs
  intro hb
  obtain ⟨path,hp⟩ := core.inhabited
  obtain ⟨pre,g,rest,he,hn,hm⟩ := (core.refines _ hs.1 _ hp).first
  have hh := core.includes (he ▸ hp)
  exact hb.missed hh hn (hf _ _ _ hh hm)

end Core
end OAI.Geometry.Hirsch.Layer.Trial
end

-- PairWeight
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Pins

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)
  {A B C D : Finset (Finset I)}

abbrev Relation (I : Type) := Finset I → Finset I → Prop

def pairMass (A B : Finset (Finset I)) (P : Relation I) :=
  ∑ s ∈ A, pins.weight s * pins.mass (B.filter (P s))

theorem pair_nonneg (P : Relation I) : 0 ≤ pins.pairMass A B P :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pins.positive _).le (pins.mass_nonneg _)

theorem pair_mono {P Q : Relation I} (ha : A ⊆ C) (hb : B ⊆ D) (hp : ∀ s ∈ A, ∀ t ∈ B, P s t → Q s t) :
    pins.pairMass A B P ≤ pins.pairMass C D Q := by
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg ha (f := fun s =>
    pins.weight s * pins.mass (D.filter (Q s))) (fun _ _ _ => mul_nonneg (pins.positive _).le (pins.mass_nonneg _)))
  apply Finset.sum_le_sum
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (pins.positive s).le
  apply pins.mass_mono
  intro t ht
  obtain ⟨ht',h⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hb ht',hp _ hs _ ht' h⟩

theorem pair_flip (A B : Finset (Finset I)) (P : Relation I) :
    pins.pairMass A B (fun s t => P t s) = pins.pairMass B A P := by
  simp only [pairMass,mass,Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pair_or (A B : Finset (Finset I)) (P Q : Relation I) :
    pins.pairMass A B (fun s t => P s t ∨ Q s t) ≤ pins.pairMass A B P + pins.pairMass A B Q := by
  unfold pairMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (pins.positive s).le
  exact (pins.mass_mono (by intro t ht; simpa [and_or_left] using ht)).trans (pins.mass_union ..)

theorem pair_full (A B : Finset (Finset I)) :
    pins.pairMass A B (fun _ _ => True) = pins.mass A * pins.mass B := by
  simp [pairMass,mass,Finset.sum_mul]

theorem pair_bound {P : Relation I} {M : ℝ} (hh : ∀ s ∈ A, pins.mass (B.filter (P s)) ≤ M) :
    pins.pairMass A B P ≤ pins.mass A * M := by
  rw [mass,Finset.sum_mul]
  exact Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hh s hs) (pins.positive _).le

theorem pair_exists {P : Relation I} {M : ℝ} (hh : pins.mass A * M < pins.pairMass A B P) :
    ∃ s ∈ A, M < pins.mass (B.filter (P s)) := by
  by_contra! hn
  exact hh.not_ge (pins.pair_bound hn)

theorem pair_exception {P : Relation I} (A B : Finset (Finset I)) :
    pins.mass (A.filter fun s => ∀ t ∈ B, P s t) * pins.mass B ≤ pins.pairMass A B P := by
  rw [← pair_full]
  exact pins.pair_mono (Finset.filter_subset ..) Finset.Subset.rfl
    (fun _ hs t ht _ => (Finset.mem_filter.mp hs).2 t ht)

end OAI.Geometry.Hirsch.Layer.Pins

namespace OAI.Geometry.Hirsch.Layer.Trial.Core

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)
  {rank : I → ℕ} (core : Core rank) (list : Finset (Finset I))

def Fails (s t : Finset I) := ∃ g ∈ s, g ∈ t ∨ ¬(core.near g).Minimal t

theorem bad_pairs {K : ℕ} {loss key : ℝ} (hk : 0 ≤ key) (hl : 0 ≤ loss)
    (hsize : ∀ s ∈ list, s.card ≤ K)
    (hkey : ∀ g, pins.mass (list.filter (g ∈ ·)) ≤ key)
    (hloss : ∀ g, (∃ s ∈ list, g ∈ s) → pins.mass (list.filter fun t => ¬(core.near g).Minimal t) ≤ loss) :
    pins.pairMass list list (fun s t => ¬core.Good s t) ≤ 2*pins.mass list * (K*(key+loss)) := by
  have one : pins.pairMass list list core.Fails ≤ pins.mass list * (K*(key+loss)) := by
    apply pins.pair_bound
    intro s hs
    let f := fun g => list.filter (g ∈ ·) ∪ list.filter (fun t => ¬(core.near g).Minimal t)
    calc
      _ ≤ ∑ g ∈ s, pins.mass (f g) := by
        apply pins.mass_cover
        intro t ht
        obtain ⟨ht,g,hg,hh⟩ := Finset.mem_filter.mp ht
        exact ⟨g,hg,by simpa [f,ht] using hh⟩
      _ ≤ ∑ _ ∈ s, (key+loss) := Finset.sum_le_sum fun g hg =>
        (pins.mass_union ..).trans (add_le_add (hkey g) (hloss g ⟨s,hs,hg⟩))
      _ ≤ _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hsize s hs)) (add_nonneg hk hl)
  have cover : ∀ s ∈ list, ∀ t ∈ list, ¬core.Good s t → core.Fails s t ∨ core.Fails t s := by
    intro s _ t _ hn
    by_contra! hh
    apply hn
    exact ⟨Finset.disjoint_left.mpr (fun g hg ht => hh.1 ⟨g,hg,.inl ht⟩),
      fun g hg => by_contra (fun ht => hh.1 ⟨g,hg,.inr ht⟩),
      fun g hg => by_contra (fun ht => hh.2 ⟨g,hg,.inr ht⟩)⟩
  have both := (pins.pair_mono Finset.Subset.rfl Finset.Subset.rfl cover).trans
    (pins.pair_or list list core.Fails (fun s t => core.Fails t s))
  rw [pins.pair_flip list list core.Fails] at both
  linarith

theorem heavy {beta : ℝ} (hc : ∀ s ∈ list, core.Cut s)
    (hb : pins.pairMass list list (fun s t => ¬core.Good s t) ≤ beta)
    (hh : 3*beta < (pins.mass list)^2) :
    (∃ s ∈ list, pins.mass list / 3 < pins.mass (list.filter (core.Newer s))) ∧
    (∃ t ∈ list, pins.mass list / 3 < pins.mass (list.filter (fun s => core.Newer s t))) := by
  let old := fun s t => core.Newer t s
  let bad := fun s t => ¬core.Good s t
  let good := fun s t => core.Newer s t ∨ old s t
  have sub : ∀ s ∈ list, ∀ t ∈ list, True → bad s t ∨ good s t := by
    intro s hs t ht _
    by_cases hg : core.Good s t
    · exact .inr (hg.order (hc _ hs) (hc _ ht))
    · exact .inl hg
  have bound := (pins.pair_mono Finset.Subset.rfl Finset.Subset.rfl sub).trans
    ((pins.pair_or list list bad good).trans (add_le_add hb (pins.pair_or list list core.Newer old)))
  rw [pins.pair_full] at bound
  have he : pins.pairMass list list old = pins.pairMass list list core.Newer :=
    pins.pair_flip list list core.Newer
  have low : pins.mass list * (pins.mass list / 3) < pins.pairMass list list core.Newer := by linarith
  exact ⟨pins.pair_exists low,pins.pair_exists (P := old) (low.trans_eq he.symm)⟩

end OAI.Geometry.Hirsch.Layer.Trial.Core
end

-- Thinning
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {Ω I : Type} [Fintype Ω] {p : Law Ω} (pins : Pins p I)

def Law.Independent (p : Law Ω) (a b : Ω → Prop) :=
  p.prob (fun x => a x ∧ b x) = p.prob a * p.prob b

namespace Pins

theorem family (s : Finset (Finset I)) : p.prob (fun x => ∃ t ∈ s, t ⊆ pins.success x) ≤ pins.mass s := by
  apply (p.union_finset s (fun t x => t ⊆ pins.success x)).trans_eq
  exact Finset.sum_congr rfl (fun t _ => pins.prob t)

theorem dynamic [Fintype I] (select : Ω → Finset (Finset I)) (event : Ω → Prop) (M K : ℕ)
    (count : ∀ x, (select x).card ≤ M) (size : ∀ x s, s ∈ select x → s.card = K)
    (active : ∀ x s, s ∈ select x → event x)
    (indep : ∀ s, p.Independent (fun x => s ∈ select x) (fun x => s ⊆ pins.success x)) :
    p.prob (fun x => ∃ s ∈ select x, s ⊆ pins.success x) ≤ M * p.prob event * pins.rate^K := by
  let valid := fun (s : Finset I) x => s ∈ select x
  have bound : ∑ s, p.prob (valid s) ≤ M * p.prob event := by
    apply p.multiplicity _ _ _ _ (fun s _ x hx => active x s hx)
    intro x
    simpa [valid] using count x
  calc
    _ ≤ ∑ s, p.prob (fun x => valid s x ∧ s ⊆ pins.success x) := p.union _
    _ = ∑ s, p.prob (valid s) * pins.rate^K := by
      apply Finset.sum_congr rfl
      intro s _
      rw [show p.prob _ = p.prob (valid s) * p.prob _ from indep s,pins.prob]
      by_cases he : s.card = K
      · rw [he]
      · have hn : ∀ x, ¬valid s x := fun x hx => he (size x s hx)
        simp [Law.prob,hn]
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right bound (pow_nonneg pins.pos.le _)

end Pins

namespace Trial

variable {Z : Type} {place : I → Z} {K e d : ℕ} {tests : Tests place e d}

theorem Tests.Available.sub {s t : Finset I} (ha : tests.Available s) (ht : t ⊆ s) : tests.Available t := by
  intro g hg
  obtain ⟨l,hl,hh⟩ := ha g (ht hg)
  exact ⟨l,hl,fun j hj hm => hh j hj (ht hm)⟩

namespace Gates

variable {pins} {gamma alpha : ℝ} [Fintype I] (gate : Gates pins place K gamma alpha)

structure Draw (fresh : Pins p I) where
  available : Ω → Finset I
  old : ∀ x, gate.Possible (available x)
  pin : ∀ x, available x ⊆ pins.success x
  independent : ∀ (E : Finset I → Prop) s,
    p.Independent (fun x => E (available x)) (fun x => s ⊆ fresh.success x)

namespace Draw

variable {gate} {fresh : Pins p I} (draw : gate.Draw fresh)

def thin (x : Ω) := draw.available x ∩ fresh.success x

omit [Fintype I] in
theorem pinned (x : Ω) : draw.thin x ⊆ pins.success x := Finset.inter_subset_left.trans (draw.pin x)

theorem large (hs : gate.Serves tests) :
    ∃ leaves : Finset I → Finset (Finset I),
      (∀ x, tests.Frontier (draw.available x) K ∅ (leaves (draw.available x))) ∧
      p.prob (fun x => tests.long.Covers (draw.available x) ∧
        ∃ s ∈ leaves (draw.available x), s.card = K ∧ s ⊆ fresh.success x) ≤
        Tests.capacity K e d * p.prob (fun x => tests.long.Covers (draw.available x)) * fresh.rate^K := by
  have hex : ∀ a, ∃ leaves, leaves.card ≤ Tests.capacity K e d ∧
      (gate.Possible a → tests.Frontier a K ∅ leaves) := by
    intro a
    by_cases hp : gate.Possible a
    · obtain ⟨x,hx⟩ := hp
      obtain ⟨leaves,hl,hf⟩ := ((hs.available x).sub hx).frontier K
      exact ⟨leaves,hl,fun _ => hf⟩
    · exact ⟨∅,by simp,fun hh => (hp hh).elim⟩
  choose leaves hc hf using hex
  refine ⟨leaves,fun x => hf _ (draw.old x),?_⟩
  let sel := fun a => (leaves a).filter (fun s => tests.long.Covers a ∧ s.card = K)
  apply le_trans _ (fresh.dynamic (sel ∘ draw.available) (fun x => tests.long.Covers (draw.available x)) _ K
    (fun x => (Finset.card_filter_le ..).trans (hc _)) (fun _ _ hh => (Finset.mem_filter.mp hh).2.2)
    (fun _ _ hh => (Finset.mem_filter.mp hh).2.1) (fun s => draw.independent (fun a => s ∈ sel a) s))
  exact p.mono (fun _ ⟨hh,s,hs,hk,hp⟩ => ⟨s,Finset.mem_filter.mpr ⟨hs,hh,hk⟩,hp⟩)

theorem extract (hs : gate.Serves tests) (near : Trial I) (paths : ℕ → Trial I) {loss U : ℝ}
    (lower : ∀ j ≤ K, (paths 0).Refines (paths (j+1)))
    (upper : (paths (K+1)).Refines tests.short)
    (hloss : ∀ j ≤ K, pins.mass ((gate.cuts (paths j) (paths (j+1))).filter (fun s => ¬near.Minimal s)) ≤ loss)
    (crude : p.prob (fun x => tests.long.Covers (draw.available x)) ≤ U) :
    p.prob (fun x => tests.long.Covers (draw.thin x) ∧
      ¬∃ s ∈ gate.cuts near (paths 0), s ⊆ draw.thin x) ≤ Tests.capacity K e d * U * fresh.rate^K + (K+1)*loss := by
  obtain ⟨leaves,hf,hl⟩ := draw.large hs
  let large := fun x => tests.long.Covers (draw.available x) ∧
    ∃ s ∈ leaves (draw.available x), s.card = K ∧ s ⊆ fresh.success x
  let bad := fun j => (gate.cuts (paths j) (paths (j+1))).filter (fun s => ¬near.Minimal s)
  let small := fun x => ∃ j ∈ Finset.range (K+1), ∃ s ∈ bad j, s ⊆ pins.success x
  have hb : p.prob small ≤ (K+1)*loss := by
    apply (p.union_finset (Finset.range (K+1)) (fun j x => ∃ s ∈ bad j, s ⊆ pins.success x)).trans
    calc
      _ ≤ ∑ _ ∈ Finset.range (K+1), loss := Finset.sum_le_sum fun j hj =>
        (pins.family _).trans (hloss j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      _ = _ := by simp
  have hlarge : p.prob large ≤ Tests.capacity K e d * U * fresh.rate^K := hl.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left crude (by positivity)) (pow_nonneg fresh.pos.le _))
  apply le_trans _ ((p.either large small).trans (add_le_add hlarge hb))
  apply p.mono
  rintro x ⟨hc,hn⟩
  have sub : draw.thin x ⊆ draw.available x := Finset.inter_subset_left
  obtain ⟨s,hm,hsub⟩ := (hf x).2 _ sub (Finset.empty_subset _) hc
  obtain ⟨⟨_,hk⟩,he | he⟩ := (hf x).1 s hm
  · exact .inl ⟨hc.mono sub,s,hm,he,hsub.trans Finset.inter_subset_right⟩
  · obtain ⟨j,hj,t,ht,hc',hmin⟩ := plateau paths hk (upper s he)
    have hthin := ht.trans hsub
    have hsize := (Finset.card_le_card ht).trans hk
    obtain ⟨y,hy⟩ := draw.old x
    have hp : gate.Possible t := ⟨y,(hthin.trans sub).trans hy⟩
    have hh : ¬near.Minimal t := fun h => hn ⟨t,gate.mem_cuts.mpr ⟨hsize,lower _ hj _ hc',h,hp⟩,hthin⟩
    exact .inr ⟨j,Finset.mem_range.mpr (by omega),t,Finset.mem_filter.mpr
      ⟨gate.mem_cuts.mpr ⟨hsize,hc',hmin,hp⟩,hh⟩,hthin.trans (draw.pinned x)⟩

end Draw
end Gates
end Trial
end OAI.Geometry.Hirsch.Layer
end

-- Resampling
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Law

variable {Ω Γ : Type} [Fintype Ω] [Fintype Γ] (p : Law Ω) (q : Law Γ)

def tensor : Law (Ω × Γ) where
  mass x := p.mass x.1 * q.mass x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum,total]

theorem tensor_mean (f : Ω × Γ → ℝ) :
    (p.tensor q).mean f = p.mean (fun x => q.mean (fun y => f (x,y))) := by
  simp only [mean,Fintype.sum_prod_type,Finset.mul_sum,tensor,mul_assoc]

theorem tensor_prob (e : Ω × Γ → Prop) :
    (p.tensor q).prob e = p.mean (fun x => q.prob (fun y => e (x,y))) := by
  simp only [← mean_ind,tensor_mean]

theorem tensor_both (e : Ω → Prop) (f : Γ → Prop) :
    (p.tensor q).prob (fun x => e x.1 ∧ f x.2) = p.prob e * q.prob f := by
  rw [← mean_ind,tensor_mean]
  simp only [← ind_mul,mean_scale,mean_ind]
  simp_rw [mul_comm _ (q.prob f)]
  rw [mean_scale,mean_ind]

theorem tensor_first (e : Ω → Prop) : (p.tensor q).prob (fun x => e x.1) = p.prob e := by
  rw [← mean_ind,tensor_mean]
  simp only [mean_const,mean_ind]

theorem preserve (f : Ω ≃ Ω) (hf : ∀ x, p.mass (f x) = p.mass x) (e : Ω → Prop) :
    p.prob (fun x => e (f x)) = p.prob e := by
  simpa only [prob,hf] using Equiv.sum_comp f (fun x => if e x then p.mass x else 0)

theorem event_loss (start stop fail : Ω → Prop) (hh : ∀ x, start x → stop x ∨ fail x) :
    p.prob start - p.prob fail ≤ p.prob stop := sub_le_iff_le_add.mpr ((p.mono hh).trans (p.either ..))

end Law

abbrev Table (Bit : Type) := Bit → Bool

namespace Table

variable {Bit Y : Type}

def Reads (s : Set Bit) (f : Table Bit → Y) := ∀ x y, Set.EqOn x y s → f x = f y

theorem Reads.mono {s t : Set Bit} {f : Table Bit → Y} (hf : Reads s f) (hs : s ⊆ t) :
    Reads t f := fun _ _ h => hf _ _ (h.mono hs)

def replace (s : Set Bit) (x y : Table Bit) : Table Bit := fun b => if b ∈ s then y b else x b

theorem Reads.replace {s : Set Bit} {f : Table Bit → Y} (hf : Reads s f) (x y) :
    f (Table.replace s x y) = f y := hf _ _ (fun _ h => by simp [Table.replace,h])

theorem Reads.keep {s : Set Bit} {f : Table Bit → Y} (hf : Reads sᶜ f) (x y) :
    f (Table.replace s x y) = f x := hf _ _ (fun b h => by simp [Table.replace,show b ∉ s from h])

def swap (s : Set Bit) (x : Table Bit × Table Bit) := (replace s x.1 x.2,replace s x.2 x.1)

theorem involution (s : Set Bit) : Function.Involutive (swap s) := by
  intro x
  ext b <;> by_cases h : b ∈ s <;> simp [swap,replace,h]

end Table

structure Coins (Bit : Type) where
  bias : Bit → ℝ
  pos : ∀ b, 0 < bias b
  le_one : ∀ b, bias b ≤ 1

namespace Coins

open Table

variable {Bit : Type} [Fintype Bit] [DecidableEq Bit] (coin : Coins Bit)

def bit (b : Bit) : Law Bool where
  mass x := if x then coin.bias b else 1-coin.bias b
  nonneg := by rintro (_ | _) <;> simp [coin.le_one,(coin.pos _).le]
  total := by simp

def law : Law (Table Bit) := Law.product coin.bit

abbrev two := coin.law.tensor coin.law

def swapped (s : Set Bit) := (involution s).toPerm (swap s)

theorem preserve (s : Set Bit) (e : Table Bit × Table Bit → Prop) :
    coin.two.prob (fun x => e (swap s x)) = coin.two.prob e := by
  apply coin.two.preserve (swapped s) _ e
  intro x
  change (∏ b, (coin.bit b).mass (Table.replace s x.1 x.2 b)) *
    (∏ b, (coin.bit b).mass (Table.replace s x.2 x.1 b)) =
    (∏ b, (coin.bit b).mass (x.1 b)) * (∏ b, (coin.bit b).mass (x.2 b))
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun b _ => by by_cases h : b ∈ s <;> simp [Table.replace,h,mul_comm])

theorem marginal (s : Set Bit) (e : Table Bit → Prop) :
    coin.two.prob (fun x => e (Table.replace s x.1 x.2)) = coin.law.prob e :=
  (coin.preserve s (fun x => e x.1)).trans (coin.law.tensor_first _ e)

theorem independent {s : Set Bit} {e f : Table Bit → Prop}
    (he : Reads sᶜ e) (hf : Reads s f) : coin.law.Independent e f := by
  unfold Law.Independent
  rw [← coin.marginal s (fun x => e x ∧ f x)]
  simp only [he.keep,hf.replace]
  exact coin.law.tensor_both _ _ _

theorem resample_both (s : Set Bit) {e f : Table Bit → Prop} (hf : Reads s f) :
    coin.two.prob (fun x => e (Table.replace s x.1 x.2) ∧ f x.1) = coin.law.prob e * coin.law.prob f := by
  rw [← coin.law.tensor_both,← coin.preserve s (fun x => e x.1 ∧ f x.2)]
  simp only [swap,hf.replace]

def All (s : Finset Bit) (x : Table Bit) := ∀ b ∈ s, x b = true

omit [Fintype Bit] [DecidableEq Bit] in
theorem reads_all (s : Finset Bit) : Reads (↑s) (All s) := fun _ _ he => propext
  ⟨fun h b hb => (he hb).symm.trans (h b hb),fun h b hb => (he hb).trans (h b hb)⟩

def weight (s : Finset Bit) := ∏ b ∈ s, coin.bias b

theorem all_prob (s : Finset Bit) : coin.law.prob (All s) = coin.weight s := by
  unfold law All
  rw [Law.independent coin.bit (fun b x => b ∈ s → x = true)]
  have he : ∀ b, (coin.bit b).prob (fun x => b ∈ s → x = true) = if b ∈ s then coin.bias b else 1 := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb,bit,Law.prob]
  simp [he,weight]

end Coins
end OAI.Geometry.Hirsch.Layer
end

-- RawBits
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [DecidableEq Bit] (coin : Coins Bit)

omit [DecidableEq Bit] in
theorem weight_pos (s : Finset Bit) : 0 < coin.weight s := Finset.prod_pos (fun b _ => coin.pos b)

omit [DecidableEq Bit] in
theorem weight_le (s : Finset Bit) : coin.weight s ≤ 1 :=
  Finset.prod_le_one (fun b _ => (coin.pos b).le) (fun b _ => coin.le_one b)

theorem weight_union (s t : Finset Bit) : coin.weight s * coin.weight t ≤ coin.weight (s ∪ t) := by
  have he : coin.weight (s ∪ t) * coin.weight (s ∩ t) = coin.weight s * coin.weight t :=
    Finset.prod_union_inter
  rw [← he]
  exact mul_le_of_le_one_right (coin.weight_pos _).le (coin.weight_le _)

theorem weight_many (s : Finset I) (f : I → Finset Bit) :
    ∏ i ∈ s, coin.weight (f i) ≤ coin.weight (s.biUnion f) := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.biUnion_insert]
    exact (mul_le_mul_of_nonneg_left ih (coin.weight_pos _).le).trans (coin.weight_union ..)

structure Raw (I : Type) where
  bits : I → Finset Bit
  rate : ℝ
  pos : 0 < rate
  weight : ∀ i, coin.weight (bits i) = rate
  unique : ∀ i j, i ≠ j → Disjoint (bits i) (bits j)

namespace Raw

variable {coin} (raw : coin.Raw I)

def bitsOf (s : Finset I) := s.biUnion raw.bits

theorem cost (s : Finset I) : coin.weight (raw.bitsOf s) = raw.rate^s.card := by
  unfold Coins.weight bitsOf
  rw [Finset.prod_biUnion (fun i _ j _ hn => raw.unique i j hn)]
  change (∏ i ∈ s, coin.weight (raw.bits i)) = _
  simp [raw.weight]

def inSite (place : I → Z) (site : Z) : Set Bit := {b | ∃ i, place i = site ∧ b ∈ raw.bits i}

omit [DecidableEq Bit] in
theorem belongs {place : I → Z} {site : Z} {i : I} {b : Bit} (hb : b ∈ raw.bits i) :
    b ∈ raw.inSite place site ↔ place i = site := by
  refine ⟨?_,fun h => ⟨i,h,hb⟩⟩
  rintro ⟨j,hj,hm⟩
  by_contra hn
  exact Finset.disjoint_left.mp (raw.unique i j (fun he => hn (he ▸ hj))) hb hm

variable [Fintype Bit] [Fintype I]

def successes (x : Table Bit) := Finset.univ.filter (fun i => All (raw.bits i) x)

omit [Fintype Bit] in
theorem all (s : Finset I) (x : Table Bit) : s ⊆ raw.successes x ↔ All (raw.bitsOf s) x := by
  simp only [successes,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [All,bitsOf,Finset.mem_biUnion]
  aesop

def pins : Pins coin.law I where
  rate := raw.rate
  pos := raw.pos
  success := raw.successes
  prob s := by rw [coin.law.eq_prob (raw.all s),coin.all_prob,raw.cost]

@[simp] theorem mem (i : I) (x : Table Bit) : i ∈ raw.pins.success x ↔ All (raw.bits i) x := by
  simp [pins,successes]

theorem reads (s : Finset I) : Reads (↑(raw.bitsOf s)) (fun x => s ⊆ raw.pins.success x) := by
  intro x y he
  exact (propext (raw.all s x)).trans ((reads_all _ _ _ he).trans (propext (raw.all s y)).symm)

theorem reads_site {place : I → Z} {site : Z} {s : Finset I} (hs : ∀ i ∈ s, place i = site) :
    Reads (raw.inSite place site) (fun x => s ⊆ raw.pins.success x) := by
  apply (raw.reads s).mono
  intro b hb
  obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hb
  exact ⟨i,hs i hi,hm⟩

theorem reads_away {place : I → Z} {site : Z} {s : Finset I} (hs : ∀ i ∈ s, place i ≠ site) :
    Reads (raw.inSite place site)ᶜ (fun x => s ⊆ raw.pins.success x) := by
  apply (raw.reads s).mono
  intro b hb
  obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hb
  exact fun hh => hs _ hi ((raw.belongs hm).mp hh)

variable (place : I → Z) (site : Z)

def after (x : Table Bit × Table Bit) := Table.replace (raw.inSite place site) x.1 x.2

theorem fixed (x : Table Bit × Table Bit) {g : I} (hg : place g ≠ site) :
    g ∈ raw.pins.success x.1 ↔ g ∈ raw.pins.success (raw.after place site x) := by
  have hh := (raw.reads_away (s := {g}) (place := place) (site := site) (by simp [hg])).keep x.1 x.2
  simpa only [Finset.singleton_subset_iff,after] using iff_of_eq hh.symm

theorem joint_after (s : Finset I) (event : Table Bit → Prop) :
    coin.two.prob (fun x => event (raw.after place site x) ∧ s ⊆ raw.pins.success x.1) =
      raw.pins.given event (s.filter (fun g => place g ≠ site)) * raw.pins.weight s := by
  let inside := s.filter fun g => place g = site
  let outside := s.filter fun g => place g ≠ site
  have he : outside ∪ inside = s := by ext; simp [inside,outside]; tauto
  have hd : Disjoint outside inside := Finset.disjoint_left.mpr fun _ h₁ h₂ =>
    (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
  let E := fun x => event x ∧ outside ⊆ raw.pins.success x
  have eqn : ∀ x, (event (raw.after place site x) ∧ s ⊆ raw.pins.success x.1) ↔
      (E (raw.after place site x) ∧ inside ⊆ raw.pins.success x.1) := by
    intro x
    have ho := (raw.reads_away (s := outside) (fun _ hg => (Finset.mem_filter.mp hg).2)).keep x.1 x.2
    unfold E after
    rw [ho,← he,Finset.union_subset_iff,and_assoc]
  have hin := raw.reads_site (s := inside) (place := place) (site := site)
    (fun _ hg => (Finset.mem_filter.mp hg).2)
  rw [coin.two.eq_prob eqn]
  change coin.two.prob (fun x => E (Table.replace _ x.1 x.2) ∧ _) = _
  rw [coin.resample_both _ hin,raw.pins.prob]
  change raw.pins.joint event outside * raw.pins.weight inside =
    raw.pins.given event outside * raw.pins.weight s
  rw [← he,raw.pins.weight_union hd,Pins.given,← mul_assoc,div_mul_cancel₀ _ (raw.pins.positive _).ne']

end Raw
end OAI.Geometry.Hirsch.Layer.Coins
end

-- Barriers
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} (raw : coin.Raw I) (place : I → Z) (site : Z)

theorem Raw.extra (s : Finset I) (f : Table Bit → Finset I) (N : ℕ) (hs : site ∉ s.image place)
    (hf : ∀ x, (f x).card ≤ N ∧ ∀ i ∈ f x, place i = site) :
    coin.two.prob (fun x => s ⊆ raw.pins.success x.1 ∧
      ∃ i ∈ f (raw.after place site x), i ∈ raw.pins.success x.1) ≤ N * raw.rate * raw.pins.weight s := by
  let A := raw.inSite place site
  let E := fun x : Table Bit × Table Bit => s ⊆ raw.pins.success x.1 ∧ ∃ i ∈ f x.1, i ∈ raw.pins.success x.2
  have hh : ∀ x : Table Bit × Table Bit, (s ⊆ raw.pins.success x.1 ∧
      ∃ i ∈ f (raw.after place site x), i ∈ raw.pins.success x.1) → E (swap A x) := by
    rintro x ⟨hp,i,hi,hm⟩
    have he : place i = site := (hf _).2 _ hi
    refine ⟨fun j hj => (raw.fixed place site x (fun h => hs (Finset.mem_image.mpr ⟨j,hj,h⟩))).mp (hp hj),
      i,hi,?_⟩
    rw [raw.mem] at hm ⊢
    intro b hb
    have ha : b ∈ A := ⟨i,he,hb⟩
    simpa [swap,Table.replace,ha] using hm b hb
  apply ((coin.two.mono hh).trans_eq (coin.preserve A E)).trans
  rw [Law.tensor_prob]
  have hb : ∀ x, coin.law.prob (fun y => E (x,y)) ≤ N * raw.rate * Law.ind (s ⊆ raw.pins.success x) := by
    intro x
    by_cases h : s ⊆ raw.pins.success x
    · have ht := raw.pins.extra ∅ (f x) (by simp)
      simp only [Pins.weight,Finset.card_empty,pow_zero,mul_one,Finset.empty_subset,true_and] at ht
      simp only [E,h,true_and,Law.ind,↓reduceIte,mul_one]
      exact ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hf x).1) raw.pos.le)
    · simp [E,h,Law.ind,Law.prob]
  apply (coin.law.mean_mono hb).trans_eq
  rw [Law.mean_scale,Law.mean_ind,raw.pins.prob]; rfl

structure Rules (raw : coin.Raw I) where
  barriers : I → Finset Bit
  separate : ∀ i j, Disjoint (barriers i) (raw.bits j)
  ok : I → Table Bit → Prop

namespace Rules

variable {raw place} (rule : Rules raw)

def pass (x : Table Bit) :=
  raw.pins.success x |>.filter (fun g => All (rule.barriers g) x ∧ rule.ok g x)

@[simp] theorem mem (x : Table Bit) (g : I) : g ∈ rule.pass x ↔
    g ∈ raw.pins.success x ∧ All (rule.barriers g) x ∧ rule.ok g x := Finset.mem_filter

def Compatible (place : I → Z) (s : Finset I) (g : I) :=
  (∀ j ∈ s, place j = place g) ∨ ∃ x, s ⊆ raw.pins.success x ∧ rule.ok g x

theorem Compatible.sub {rule : Rules raw} {s t : Finset I} {g : I}
    (h : rule.Compatible place s g) (ht : t ⊆ s) : rule.Compatible place t g := by
  rcases h with h | ⟨x,hx,hh⟩
  · exact .inl (fun j hj => h j (ht hj))
  · exact .inr ⟨x,ht.trans hx,hh⟩

structure Reliable (place : I → Z) (K : ℕ) (margin loss : ℝ) : Prop where
  pos : 0 < margin
  small : margin ≤ 1
  nonneg : 0 ≤ loss
  barriers : ∀ i, margin ≤ coin.weight (rule.barriers i)
  screen : ∀ g s, s.card ≤ K → rule.Compatible place s g → raw.pins.given (fun x => ¬rule.ok g x) s ≤ loss

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem barriers_keep (site : Z) (x : Table Bit × Table Bit) (g : I) :
    All (rule.barriers g) x.1 → All (rule.barriers g) (raw.after place site x) := by
  intro hh b hb
  have hn : b ∉ raw.inSite place site := by
    rintro ⟨j,_,hj⟩
    exact Finset.disjoint_left.mp (rule.separate g j) hb hj
  simpa [Raw.after,Table.replace,hn] using hh _ hb

variable {rule} {K : ℕ} {margin loss : ℝ} (hr : rule.Reliable place K margin loss)

include hr in
theorem Reliable.start {s : Finset I} (hk : s.card ≤ K) :
    margin^K * raw.pins.weight s ≤
      coin.law.prob (fun x => s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x) := by
  let bars := s.biUnion rule.barriers
  have he : ∀ x, (s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x) ↔
      All (bars ∪ raw.bitsOf s) x := by
    intro x
    change (s ⊆ raw.successes x ∧ _) ↔ _
    rw [raw.all]
    simp only [All,bars,Finset.mem_union,Finset.mem_biUnion]
    aesop
  rw [coin.law.eq_prob he,coin.all_prob]
  apply le_trans _ (coin.weight_union ..)
  rw [raw.cost]
  apply mul_le_mul_of_nonneg_right _ (raw.pins.positive s).le
  apply le_trans _ (coin.weight_many s rule.barriers)
  apply (pow_le_pow_of_le_one hr.pos.le hr.small hk).trans
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => hr.pos.le) (fun i _ => hr.barriers i)

end Rules
end OAI.Geometry.Hirsch.Layer.Coins
end

-- JointGates
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins.Rules

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} {raw : coin.Raw I} {place : I → Z} {rule : Rules raw}
  {K : ℕ} {margin loss gamma alpha : ℝ} (hr : rule.Reliable place K margin loss)
  {s : Finset I} (hk : s.card ≤ K) (hc : ∀ g ∈ s, rule.Compatible place s g)

include hr hk hc in
theorem Reliable.failures (site : Z) :
    coin.two.prob (fun x => ∃ g ∈ s, s ⊆ raw.pins.success x.1 ∧
      (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))) ≤ 2*K*loss*raw.pins.weight s := by
  let fail := fun g (x : Table Bit × Table Bit) => s ⊆ raw.pins.success x.1 ∧
    (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))
  have each : ∀ g ∈ s, coin.two.prob (fail g) ≤ 2*loss*raw.pins.weight s := by
    intro g hg
    let bad := fun t => ¬rule.ok g t
    let orig := fun x : Table Bit × Table Bit => bad x.1 ∧ s ⊆ raw.pins.success x.1
    let later := fun x : Table Bit × Table Bit => bad (raw.after place site x) ∧ s ⊆ raw.pins.success x.1
    have h₁ : coin.two.prob orig ≤ loss * raw.pins.weight s := by
      rw [show coin.two.prob orig = raw.pins.joint bad s from coin.law.tensor_first _ (fun y => bad y ∧ s ⊆ raw.pins.success y)]
      exact (div_le_iff₀ (raw.pins.positive s)).mp (hr.screen g s hk (hc g hg))
    have h₂ : coin.two.prob later ≤ loss * raw.pins.weight s := by
      unfold later
      rw [raw.joint_after]
      apply mul_le_mul_of_nonneg_right _ (raw.pins.positive s).le
      exact hr.screen g _ ((Finset.card_filter_le ..).trans hk) ((hc g hg).sub (Finset.filter_subset ..))
    apply le_trans _ ((coin.two.either orig later).trans (show _ ≤ 2*loss*raw.pins.weight s by linarith))
    exact coin.two.mono fun _ ⟨hp,h⟩ => h.imp (fun h => ⟨h,hp⟩) (fun h => ⟨h,hp⟩)
  calc
    _ ≤ ∑ g ∈ s, coin.two.prob (fail g) := coin.two.union_finset ..
    _ ≤ ∑ _ ∈ s, 2*loss*raw.pins.weight s := Finset.sum_le_sum each
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hn := hr.nonneg
      have hp := raw.pins.positive s
      linarith [mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk : (s.card : ℝ) ≤ K)
        (show 0 ≤ 2*loss*raw.pins.weight s by positivity)]

include hr hk hc in
theorem Reliable.joint (site : Z) (hg : gamma ≤ margin^K - 2*K*loss) :
    gamma * raw.pins.weight s ≤ coin.two.prob (fun x => s ⊆ rule.pass x.1 ∧
      ∀ g ∈ s, place g ≠ site → g ∈ rule.pass (raw.after place site x)) := by
  let start := fun x => s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x
  let stop := fun x : Table Bit × Table Bit => s ⊆ rule.pass x.1 ∧
    ∀ g ∈ s, place g ≠ site → g ∈ rule.pass (raw.after place site x)
  let fail := fun x : Table Bit × Table Bit => ∃ g ∈ s, s ⊆ raw.pins.success x.1 ∧
    (¬rule.ok g x.1 ∨ ¬rule.ok g (raw.after place site x))
  have cover : ∀ x, start x.1 → stop x ∨ fail x := by
    intro x hx
    by_cases hn : fail x
    · exact .inr hn
    have pass : ∀ g ∈ s, rule.ok g x.1 ∧ rule.ok g (raw.after place site x) := by
      intro g h
      exact ⟨by_contra (fun hh => hn ⟨g,h,hx.1,.inl hh⟩),by_contra (fun hh => hn ⟨g,h,hx.1,.inr hh⟩)⟩
    left
    exact ⟨fun g h => (rule.mem ..).mpr ⟨hx.1 h,hx.2 g h,(pass g h).1⟩,fun g h he =>
      (rule.mem ..).mpr ⟨(raw.fixed place site x he).mp (hx.1 h),
        rule.barriers_keep site x g (hx.2 g h),(pass g h).2⟩⟩
  have low : margin^K * raw.pins.weight s ≤ coin.two.prob (fun x => start x.1) :=
    (hr.start hk).trans_eq (coin.law.tensor_first _ start).symm
  have high : coin.two.prob fail ≤ 2*K*loss*raw.pins.weight s := hr.failures hk hc site
  apply le_trans _ (coin.two.event_loss _ _ _ cover)
  linarith [mul_le_mul_of_nonneg_right hg (raw.pins.positive s).le]

include hr hk hc in
theorem Reliable.passage [Nonempty Z] (hg : gamma ≤ margin^K - 2*K*loss) :
    gamma * raw.pins.weight s ≤ coin.law.prob (fun x => s ⊆ rule.pass x) := by
  rw [← coin.law.tensor_first coin.law (fun x => s ⊆ rule.pass x)]
  exact (hr.joint hk hc (Classical.arbitrary Z) hg).trans (coin.two.mono (fun _ h => h.1))

theorem compatible_of_possible (hs : ∃ x, s ⊆ rule.pass x) : ∀ g ∈ s, rule.Compatible place s g := by
  obtain ⟨x,hx⟩ := hs
  exact fun g hg => .inr ⟨x,hx.trans (Finset.filter_subset ..),((rule.mem ..).mp (hx hg)).2.2⟩

variable [Nonempty Z] (hg : gamma ≤ margin^K - 2*K*loss) (thr : Thresholds K)
  (bad : I → Table Bit → Prop) (screened : ∀ g x, rule.ok g x → raw.pins.Screen thr (bad g) x)

def Reliable.gates : Trial.Gates raw.pins place K gamma (thr.value K) where
  pass := rule.pass
  pinned _ := Finset.filter_subset ..
  bad := bad
  screen x g hh := (screened g x ((rule.mem ..).mp hh).2.2).1
  possible _ hk hs := hr.passage hk (compatible_of_possible hs) hg
  compatible x g hh s hs hk := ((screened g x ((rule.mem ..).mp hh).2.2).2 s
    (hs.trans (Finset.filter_subset ..)) hk).trans (thr.mono hk)

theorem Reliable.resample (site : Z) : Nonempty ((hr.gates hg thr bad screened).Resample site) := by
  refine ⟨{
    Resp := Table Bit × Table Bit, law := coin.two, before := Prod.fst, after := raw.after place site,
    marginal := coin.marginal _, fixed := fun x g => raw.fixed place site x,
    extra := raw.extra place site, possible := fun s hk hs => hr.joint hk (compatible_of_possible hs) site hg }⟩

end OAI.Geometry.Hirsch.Layer.Coins.Rules
end

-- Screening
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} {raw : coin.Raw I} {place : I → Z}
  {K : ℕ} {margin loss : ℝ}

namespace Rules

def initial (raw : coin.Raw I) : Rules raw where
  barriers _ := ∅
  separate _ _ := Finset.disjoint_empty_left _
  ok _ _ := True

theorem initial_reliable (raw : coin.Raw I) (place : I → Z) (K : ℕ) :
    (initial raw).Reliable place K 1 0 := by
  refine ⟨one_pos,le_rfl,le_rfl,fun _ => by simp [initial,weight],?_⟩
  intro g s _ _
  simp [initial,Pins.given,Pins.joint,Law.prob]

variable (rule : Rules raw) (thr : Thresholds K) (bad : I → Table Bit → Prop)

def screen : Rules raw :=
  { rule with ok := fun g x => rule.ok g x ∧ raw.pins.Screen thr (bad g) x }

theorem screen_pass (x : Table Bit) : (rule.screen thr bad).pass x ⊆ rule.pass x := by
  intro g hg
  obtain ⟨hp,hb,hs,_⟩ := (mem ..).mp hg
  exact (mem ..).mpr ⟨hp,hb,hs⟩

theorem reliable_screen (hr : rule.Reliable place K margin loss)
    (ignore : ∀ g s, s.card ≤ K → (∀ i ∈ s, place i = place g) → raw.pins.given (bad g) s ≤ thr.value 0) :
    (rule.screen thr bad).Reliable place K margin (loss + (1+4^K)*thr.value K) := by
  refine ⟨hr.pos,hr.small,?_,hr.barriers,fun g s hk hc => ?_⟩
  · have := thr.positive K
    exact add_nonneg hr.nonneg (by positivity)
  · have old : rule.Compatible place s g := hc.imp_right (fun ⟨x,hx,h,_⟩ => ⟨x,hx,h⟩)
    have compatible : raw.pins.Compatible thr (bad g) s := by
      rcases hc with hh | ⟨x,hx,_,hs⟩
      · exact fun t ht hk => (ignore g t hk (fun i hi => hh i (ht hi))).trans (thr.mono (by omega))
      · exact raw.pins.passes thr _ hs hx
    have h₁ := hr.screen g s hk old
    have h₂ := raw.pins.screen_cost thr (bad g) hk compatible
    rw [← Pins.cond_prob] at h₁ h₂ ⊢
    exact ((raw.pins.cond s).mono (fun _ h => not_and_or.mp h)).trans
      (((raw.pins.cond s).either _ _).trans (add_le_add h₁ h₂))

end Rules

namespace Raw

variable (raw fresh : coin.Raw I)

def Separate := ∀ i j, Disjoint (raw.bits i) (fresh.bits j)

def join (hd : raw.Separate fresh) : coin.Raw I where
  bits i := raw.bits i ∪ fresh.bits i
  rate := raw.rate * fresh.rate
  pos := mul_pos raw.pos fresh.pos
  weight i := by unfold Coins.weight; rw [Finset.prod_union (hd i i)]; exact congrArg₂ (· * ·) (raw.weight i) (fresh.weight i)
  unique i j h := by
    rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
    exact ⟨⟨raw.unique i j h,hd i j⟩,⟨(hd j i).symm,fresh.unique i j h⟩⟩

theorem join_success (hd : raw.Separate fresh) (x : Table Bit) :
    (raw.join fresh hd).pins.success x = raw.pins.success x ∩ fresh.pins.success x := by
  ext i
  simp only [Finset.mem_inter,mem,join,All,Finset.mem_union]
  aesop

theorem join_given (hd : raw.Separate fresh) (e : Table Bit → Prop)
    (he : Reads (↑(fresh.bitsOf Finset.univ))ᶜ e) (s : Finset I) :
    (raw.join fresh hd).pins.given e s = raw.pins.given e s := by
  let A : Set Bit := ↑(fresh.bitsOf Finset.univ)
  have hp : Reads Aᶜ (fun x => s ⊆ raw.pins.success x) := by
    apply (raw.reads s).mono
    intro b hb hh
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hh
    exact Finset.disjoint_left.mp (hd i j) hi hj
  have hq : Reads A (fun x => s ⊆ fresh.pins.success x) := by
    apply (fresh.reads s).mono
    intro b hb
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩
  have hi := coin.independent (e := fun x => e x ∧ s ⊆ raw.pins.success x)
    (fun x y h => congrArg₂ And (he x y h) (hp x y h)) hq
  unfold Pins.given Pins.joint
  simp only [join_success,Finset.subset_inter_iff,← and_assoc]
  rw [hi,fresh.pins.prob]
  change _ * fresh.rate^s.card / (raw.rate * fresh.rate)^s.card = _
  rw [mul_pow,mul_div_mul_right _ _ (pow_ne_zero _ fresh.pos.ne')]; rfl

end Raw

namespace Rules

variable {fresh : coin.Raw I} (rule : Rules raw) (hd : raw.Separate fresh)
  (bars : I → Finset Bit) (sep : ∀ i j, Disjoint (rule.barriers i ∪ bars i) ((raw.join fresh hd).bits j))

def next : Rules (raw.join fresh hd) where
  barriers i := rule.barriers i ∪ bars i
  separate := sep
  ok := rule.ok

theorem next_pass (x : Table Bit) (g : I) :
    g ∈ (rule.next hd bars sep).pass x ↔
      g ∈ rule.pass x ∧ g ∈ fresh.pins.success x ∧ All (bars g) x := by
  rw [mem,Raw.join_success,mem,Finset.mem_inter]
  simp only [next,All,Finset.mem_union]
  aesop

theorem reliable_next (hr : rule.Reliable place K margin loss)
    (hdep : ∀ g, Reads (↑(fresh.bitsOf Finset.univ))ᶜ (rule.ok g))
    {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1) (hb : ∀ g, v ≤ coin.weight (bars g)) :
    (rule.next hd bars sep).Reliable place K (margin*v) loss := by
  refine ⟨mul_pos hr.pos hv,(mul_le_of_le_one_left hv.le hr.small).trans hv',hr.nonneg,fun i => ?_,fun g s hk hc => ?_⟩
  · exact (mul_le_mul (hr.barriers i) (hb i) hv.le (coin.weight_pos _).le).trans (coin.weight_union ..)
  · have old : rule.Compatible place s g := by
      rcases hc with hc | ⟨x,hx,hh⟩
      · exact .inl hc
      · rw [Raw.join_success] at hx
        exact .inr ⟨x,hx.trans Finset.inter_subset_left,hh⟩
    change (raw.join fresh hd).pins.given (fun x => ¬rule.ok g x) s ≤ loss
    rw [raw.join_given fresh hd _ (fun x y h => congrArg Not (hdep g x y h))]
    exact hr.screen g s hk old

end Rules
end OAI.Geometry.Hirsch.Layer.Coins
end

-- LocalBits
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins.Raw

open Table

variable {Bit I : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} (raw : coin.Raw I)

def force (s : Finset I) (x : Table Bit) := Table.replace (↑(raw.bitsOf s)) x (fun _ => true)

theorem forced (s : Finset I) (e : Table Bit → Prop) :
    coin.law.prob (fun x => e (raw.force s x)) = raw.pins.given e s := by
  let A : Set Bit := ↑(raw.bitsOf s)
  have fixed : ∀ x, s ⊆ raw.pins.success x → raw.force s x = x := by
    intro x hx
    have hh := (raw.all s x).mp hx
    funext b
    by_cases hb : b ∈ raw.bitsOf s
    · simp [force,Table.replace,hb,hh b hb]
    · simp [force,Table.replace,hb]
  have free : Reads Aᶜ (fun x => e (raw.force s x)) := by
    intro x y hh
    apply congrArg e
    funext b
    by_cases hb : b ∈ raw.bitsOf s
    · simp [force,Table.replace,hb]
    · simp [force,Table.replace,hb,hh (show b ∈ Aᶜ from hb)]
  have hi := coin.independent free (raw.reads s)
  apply (eq_div_iff (raw.pins.positive s).ne').mpr
  change _ * raw.pins.rate^s.card = _
  rw [← raw.pins.prob,← hi]
  apply coin.law.eq_prob
  intro x
  by_cases hh : s ⊆ raw.pins.success x
  · simp only [fixed _ hh]
  · simp [hh]

theorem given_restrict {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e) (keys : Finset I)
    (hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A) (s : Finset I) :
    raw.pins.given e s = raw.pins.given e (s ∩ keys) := by
  rw [← forced,← forced]
  apply coin.law.eq_prob
  intro x
  apply iff_of_eq
  apply he
  intro b hb
  have same : b ∈ raw.bitsOf s ↔ b ∈ raw.bitsOf (s ∩ keys) := by
    simp only [bitsOf,Finset.mem_biUnion,Finset.mem_inter]
    exact ⟨fun ⟨j,hj,hm⟩ => ⟨j,⟨hj,by_contra (fun hn => hk j hn b hm hb)⟩,hm⟩,
      fun ⟨j,hj,hm⟩ => ⟨j,hj.1,hm⟩⟩
  simp only [force,Table.replace,Finset.mem_coe,same]

theorem screen_restrict {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e) (keys : Finset I)
    (hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A) {K : ℕ} (thr : Thresholds K) (x : Table Bit) :
    raw.pins.Screen thr e x ↔ ¬e x ∧ raw.pins.Compatible thr e (raw.pins.success x ∩ keys) := by
  refine ⟨fun h => ⟨h.1,raw.pins.passes thr e h Finset.inter_subset_left⟩,fun ⟨hn,hc⟩ => ⟨hn,?_⟩⟩
  intro s hs hm
  have hh := Finset.card_le_card (Finset.inter_subset_left : s ∩ keys ⊆ s)
  rw [raw.given_restrict he keys hk]
  exact (hc _ (Finset.inter_subset_inter hs Finset.Subset.rfl) (hh.trans hm)).trans (thr.mono hh)

theorem reads_screen {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e)
    (whole : ∀ j b, b ∈ raw.bits j → b ∈ A → ↑(raw.bits j) ⊆ A) {K : ℕ} (thr : Thresholds K) :
    Reads A (raw.pins.Screen thr e) := by
  let keys := Finset.univ.filter (fun j => ↑(raw.bits j) ⊆ A)
  have hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A := by
    intro j hj b hb hm
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,whole j b hb hm⟩)
  intro x y hh
  have same : raw.pins.success x ∩ keys = raw.pins.success y ∩ keys := by
    ext j
    by_cases hj : j ∈ keys
    · have hv := ((reads_all (raw.bits j)).mono (Finset.mem_filter.mp hj).2) x y hh
      simp only [Finset.mem_inter,hj,and_true,mem,hv]
    · simp [hj]
  apply propext
  rw [raw.screen_restrict he keys hk,raw.screen_restrict he keys hk,same,he x y hh]

end OAI.Geometry.Hirsch.Layer.Coins.Raw
end

-- Board
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Board (I : Type) (n : ℕ) := World I (n*3)

namespace Board

variable {I : Type} {n : ℕ} (w : Board I n)

def place (i : I) := w.layer i / 3
def Middle (i : I) := w.layer i % 3 = 1
def Shore (d : Bool) (i : I) := w.layer i % 3 = if d then 2 else 0

def loc (d : Bool) (i : I) := if d then w.layer i else n*3-1-w.layer i

def num (d : Bool) (i : I) := w.loc d i / 3

theorem num_lt (d : Bool) (i : I) : w.num d i < n := by
  have := w.bound i
  unfold num loc
  split <;> omega

theorem same (d : Bool) (i j : I) : w.num d i = w.num d j ↔ w.place i = w.place j := by
  have := w.bound i
  have := w.bound j
  cases d <;> simp [num,loc,place]; omega

theorem reverse (d : Bool) (i : I) : w.num (!d) i + w.num d i + 1 = n := by
  have := w.bound i
  cases d <;> simp [num,loc] <;> omega

theorem loc_step (d : Bool) {i : I} (hi : w.live i) : w.loc d (w.step i d) = w.loc d i + 1 := by
  have := w.bound i
  have := w.east i hi
  have := w.west i hi
  cases d <;> simp [loc] <;> omega

theorem shore_loc (d : Bool) (i : I) : w.Shore d i ↔ w.loc d i % 3 = 2 := by
  have := w.bound i
  cases d <;> simp [Shore,loc]; omega

theorem middle_loc (d : Bool) (i : I) : w.Middle i ↔ w.loc d i % 3 = 1 := by
  have := w.bound i
  cases d <;> simp [Middle,loc]; omega

theorem middle_step {i : I} (hm : w.Middle i) (hl : w.live i) (d : Bool) :
    w.Shore d (w.step i d) ∧ w.place (w.step i d) = w.place i := by
  have := w.loc_step d hl
  have := (w.middle_loc d i).mp hm
  rw [w.shore_loc,← w.same d]
  unfold num
  omega

structure Round where
  mark : I → Bool → Prop
  middle : ∀ i d, mark i d → w.Middle i ∧ w.live i
  jump : I → Bool → I → Prop
  localJump : ∀ i d j, jump i d j → w.live i ∧ w.layer j = w.layer i ∧ w.rank j < w.rank i

abbrev Budget := ℕ → ℕ

def flat (d : ℕ) : Budget := fun _ => d

def atLayer (j : ℕ) : Budget := fun k => if k = j then 1 else 0

def ahead (d : Bool) (i : I) : Budget :=
  fun j => if (if d then w.layer i ≤ j else j ≤ w.layer i) then 1 else 0

theorem ahead_one (d : Bool) (i : I) : w.ahead d i ≤ flat 1 := by intro j; simp only [ahead,flat]; split_ifs <;> omega

theorem ahead_step (d : Bool) {i : I} (hi : w.live i) :
    atLayer (w.layer i) + w.ahead d (w.step i d) = w.ahead d i := by
  have := w.east i hi
  have := w.west i hi
  ext j
  cases d <;> simp only [atLayer,ahead,Pi.add_apply,Bool.false_eq_true,↓reduceIte] <;> split_ifs <;> omega

namespace Round

variable {w} (r : w.Round)

def charge (i : I) (d : Bool) : List I := if r.mark i d then [w.step i d] else []

theorem charge_mem {i j : I} {d : Bool} : j ∈ r.charge i d ↔ r.mark i d ∧ j = w.step i d := by
  by_cases h : r.mark i d <;> simp [charge,h]

def Move (i : I) (d : Bool) (j : I) := w.live i ∧ (j = w.step i d ∨ r.jump i d j)

theorem basic {i : I} (hi : w.live i) (d : Bool) : r.Move i d (w.step i d) := ⟨hi,.inl rfl⟩

theorem falls {i j : I} {d : Bool} (hm : r.Move i d j) : w.rank j < w.rank i := by
  rcases hm with ⟨hl,rfl | hh⟩
  · exact w.decrease _ hl _
  · exact (r.localJump _ _ _ hh).2.2

inductive Trip (area : Set ℕ) : I → I → Budget → List I → Prop
  | nil {i b} : Trip area i i b []
  | go {i j k d b a path} (inside : w.place i ∈ area) (move : r.Move i d j)
      (allow : atLayer (w.layer i) + a ≤ b) (tail : Trip area j k a path) :
      Trip area i k b (r.charge i d ++ path)

def Ends (w : Board I n) (area : Set ℕ) (d : Bool) (i : I) :=
  (w.place i ∈ area ∧ ¬w.live i) ∨ (w.place i ∉ area ∧ w.Shore (!d) i)

def test (area : Set ℕ) (d : Bool) (b : Budget) (i : I) : Trial I :=
  {path | ∃ j, Ends w area d j ∧ r.Trip area i j b path}

def paths (area : Set ℕ) (b : Budget) (i : I) : Trial I :=
  {path | ∃ j, r.Trip area i j b path}

variable {r} {area : Set ℕ} {i j k : I} {a b c : Budget} {path path' : List I}

theorem Trip.more (h : r.Trip area i j a path) (hb : a ≤ b) : r.Trip area i j b path := by
  cases h with
  | nil => exact .nil
  | go hi hm ha ht => exact .go hi hm (ha.trans hb) ht

theorem Trip.append (h : r.Trip area i j a path) (h' : r.Trip area j k b path') :
    r.Trip area i k (a+b) (path ++ path') := by
  induction h with
  | nil => exact h'.more (fun _ => Nat.le_add_left ..)
  | go hi hm ha ht ih =>
    rw [List.append_assoc]
    exact .go hi hm (by rw [← add_assoc]; exact add_le_add_left ha _) (ih h')

theorem Trip.widen (h : r.Trip area i j a path) {s : Set ℕ} (hs : area ⊆ s) : r.Trip s i j a path := by
  induction h with
  | nil => exact .nil
  | go hi hm ha ht ih => exact .go (hs hi) hm ha ih

theorem Trip.rank (h : r.Trip area i j a path) : w.rank j ≤ w.rank i := by
  induction h with
  | nil => rfl
  | go hi hm ha ht ih => exact ih.trans (r.falls hm).le

theorem Trip.member (h : r.Trip area i j a path) {g : I} (hg : g ∈ path) :
    w.place g ∈ area ∧ w.rank g < w.rank i := by
  induction h with
  | nil => simp at hg
  | go hi hm ha ht ih =>
    rcases List.mem_append.mp hg with hh | hh
    · obtain ⟨hc,rfl⟩ := r.charge_mem.mp hh
      exact ⟨(w.middle_step (r.middle _ _ hc).1 hm.1 _).2.symm ▸ hi,w.decrease _ hm.1 _⟩
    · exact ⟨(ih hh).1,(ih hh).2.trans (r.falls hm)⟩

theorem test_mono (r : w.Round) (area : Set ℕ) (d : Bool) (i : I) (h : a ≤ b) :
    (r.test area d a i).Refines (r.test area d b i) := by
  rintro s hs path ⟨j,hj,hp⟩
  exact hs path ⟨j,hj,hp.more h⟩

end Round
end Board
end OAI.Geometry.Hirsch.Layer
end

-- Redirect
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Round

variable {I : Type} {n : ℕ} {w : Board I n}
  {r q : w.Round} {area : Set ℕ} {i j k g : I} {a b c : Budget} {path pre rest : List I}

theorem Trip.split (h : r.Trip area i j b path) (he : path = pre ++ g :: rest) :
    ∃ u d a, r.Trip area i u a pre ∧ w.place u ∈ area ∧ r.mark u d ∧
      w.step u d = g ∧ a + atLayer (w.layer u) ≤ b := by
  induction h generalizing pre with
  | nil => simp at he
  | @go i j k d b a path hi hm ha ht ih =>
    have more : ∀ l, path = l ++ g :: rest → pre = r.charge i d ++ l →
        ∃ u e f, r.Trip area i u f pre ∧ w.place u ∈ area ∧ r.mark u e ∧
          w.step u e = g ∧ f + atLayer (w.layer u) ≤ b := by
      intro l he' he''
      obtain ⟨u,e,f,hf,hu,hg,hkey,hb⟩ := ih he'
      rw [he'']
      exact ⟨u,e,_,.go hi hm le_rfl hf,hu,hg,hkey,by
        rw [add_assoc]; exact (add_le_add_right hb _).trans ha⟩
    by_cases hc : r.mark i d
    swap
    · exact more pre (by simpa [charge,hc] using he) (by simp [charge,hc])
    cases pre with
    | nil =>
      have hg : w.step i d = g := (List.cons.inj (by simpa only [charge,if_pos hc,
        List.singleton_append,List.nil_append] using he)).1
      exact ⟨i,d,0,.nil,hi,hc,hg,by simpa using (le_self_add.trans ha)⟩
    | cons x l =>
      simp only [charge,if_pos hc,List.cons_append,List.nil_append,List.cons.injEq] at he
      exact more l he.2 (by simp [charge,hc,he.1])

theorem Trip.step (hi : w.place i ∈ area) {d : Bool} (hm : r.Move i d j) :
    r.Trip area i j (atLayer (w.layer i)) (r.charge i d) := by
  simpa using Trip.go hi hm (le_refl (atLayer (w.layer i) + 0)) (.nil (b := 0))

theorem Trip.redirect (h : r.Trip area i j b (pre ++ g :: rest)) :
    r.Trip area i g b (pre ++ [g]) := by
  obtain ⟨u,d,a,hp,hu,hc,rfl,hb⟩ := h.split rfl
  simpa [charge,hc] using (hp.append (.step hu (r.basic (r.middle _ _ hc).2 d))).more hb

theorem Trip.carry {d : Bool} {s : Finset I} (h : r.Trip area i j a path)
    (hn : ¬Trial.Hit s path) (hc : (r.test area d c i).Covers s) (hb : a+b ≤ c) :
    (r.test area d b j).Covers s := by
  rintro l ⟨v,hv,ht⟩
  obtain ⟨g,hg,hs⟩ := hc _ ⟨v,hv,(h.append ht).more hb⟩
  exact ⟨g,(List.mem_append.mp hg).resolve_left (fun hh => hn ⟨g,hh,hs⟩),hs⟩

theorem transfers (d : Bool) (hb : a+b ≤ c) :
    (r.paths area a i).Transfers (r.test area d c i) (r.test area d b) := by
  rintro pre g rest ⟨j,hp⟩ s hc hn hg
  apply hp.redirect.carry _ hc hb
  rintro ⟨v,hv,hs⟩
  rcases List.mem_append.mp hv with hh | hh
  · exact hn ⟨v,hh,hs⟩
  · exact hg (List.mem_singleton.mp hh ▸ hs)

theorem Trip.bound (h : r.Trip area i j b path) (x : ℕ) :
    (Trial.keysAt w.place path {x}).card ≤ b (3*x+1) := by
  induction h with
  | nil => simp [Trial.keysAt]
  | @go i j k d b a path hi hm ha ht ih =>
    have hh := ha (3*x+1)
    simp only [Pi.add_apply] at hh
    by_cases hc : r.mark i d
    swap
    · simpa [charge,hc] using ih.trans (Nat.le_add_left .. |>.trans hh)
    have mid := (r.middle _ _ hc).1
    have eq := (w.middle_step mid hm.1 d).2
    by_cases hx : w.place i = x
    · have he : 3*x+1 = w.layer i := by unfold Middle at mid; unfold place at hx; omega
      simp only [atLayer,if_pos he] at hh
      have sub : Trial.keysAt w.place (r.charge i d ++ path) {x} ⊆
          insert (w.step i d) (Trial.keysAt w.place path {x}) := by
        intro v hv; simp [charge,hc] at hv ⊢; tauto
      have := (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
      omega
    · have he : Trial.keysAt w.place (r.charge i d ++ path) {x} =
          Trial.keysAt w.place path {x} := by
        ext v; simp [charge,hc]; grind
      rw [he]; omega

def tests (r : w.Round) (area : Set ℕ) (dir : Bool) (i : I) (a b : Budget) (e d : ℕ)
    (he : a ≤ flat e) (hb : a + flat d ≤ b) : Trial.Tests w.place e d where
  short := r.test area dir a i
  long := r.test area dir b i
  next := r.test area dir (flat d)
  refines := test_mono _ _ _ _ (le_self_add.trans hb)
  transfer := fun pre g rest ⟨j,_,ht⟩ => transfers dir hb pre g rest ⟨j,ht⟩
  shortBound := fun _ ⟨_,_,ht⟩ x => (ht.bound x).trans (he _)
  nextBound := fun _ _ ⟨_,_,ht⟩ x => ht.bound x

structure Finer (q r : w.Round) : Prop where
  marks : ∀ i d, q.mark i d → r.mark i d
  jumps : ∀ i d j, r.jump i d j → q.jump i d j

theorem Finer.refl (r : w.Round) : r.Finer r := ⟨fun _ _ h => h,fun _ _ _ h => h⟩

theorem Finer.trans {u : w.Round} (h : u.Finer q) (h' : q.Finer r) : u.Finer r :=
  ⟨fun i d hi => h'.marks i d (h.marks i d hi),fun i d j hj => h.jumps i d j (h'.jumps i d j hj)⟩

theorem Finer.trip (h : q.Finer r) (ht : r.Trip area i j b path) :
    ∃ l, q.Trip area i j b l ∧ l ⊆ path := by
  induction ht with
  | nil => exact ⟨[],.nil,fun _ hh => hh⟩
  | go hi hm ha ht ih =>
    obtain ⟨l,hl,hs⟩ := ih
    refine ⟨_,.go hi ⟨hm.1,hm.2.imp_right (h.jumps _ _ _)⟩ ha hl,?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hh | hh
    · obtain ⟨hc,he⟩ := q.charge_mem.mp hh
      exact List.mem_append_left _ (r.charge_mem.mpr ⟨h.marks _ _ hc,he⟩)
    · exact List.mem_append_right _ (hs hh)

theorem Finer.test (h : q.Finer r) {d : Bool} (hb : a ≤ b) :
    (r.test area d a i).Refines (q.test area d b i) := by
  rintro s hc path ⟨j,hj,ht⟩
  obtain ⟨l,hl,hs⟩ := h.trip ht
  obtain ⟨g,hg,hm⟩ := hc _ ⟨j,hj,hl.more hb⟩
  exact ⟨g,hs hg,hm⟩

end OAI.Geometry.Hirsch.Layer.Board.Round
end

-- Rays
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I : Type} {n : ℕ} (w : Board I n)

theorem shore_inj {d e : Bool} {i : I} (h : w.Shore d i) (h' : w.Shore e i) : d = e := by
  cases d <;> cases e <;> simp_all [Shore]

theorem shore_cross {i : I} {d : Bool} (hi : w.live i) (h : w.place (w.step i d) ≠ w.place i) :
    w.Shore (!d) (w.step i d) := by
  have := w.east i hi
  have := w.west i hi
  cases d <;> simp [place,Shore] at * <;> omega

inductive Ray (area : Set ℕ) (d : Bool) : I → I → Prop
  | self {i} : Ray area d i i
  | go {i j} (hi : w.place i ∈ area) (hl : w.live i) (rest : Ray area d (w.step i d) j) :
      Ray area d i j

variable {w} {area : Set ℕ} {d : Bool} {i j k g : I}

theorem Ray.join (h : w.Ray area d i j) (h' : w.Ray area d j k) : w.Ray area d i k := by
  induction h with
  | self => exact h'
  | go hi hl ht ih => exact .go hi hl (ih h')

theorem Ray.forward (h : w.Ray area d i j) : w.loc d i ≤ w.loc d j := by
  induction h with
  | self => rfl
  | go hi hl ht ih => rw [w.loc_step d hl] at ih; omega

theorem Ray.ordered (h : w.Ray area d i j) (h' : w.Ray area d i k)
    (hle : w.loc d j ≤ w.loc d k) : w.Ray area d j k := by
  induction h with
  | self => exact h'
  | go hi hl ht ih =>
    cases h' with
    | self => have := ht.forward; rw [w.loc_step d hl] at this; omega
    | go _ _ ht' => exact ih ht' hle

theorem Ray.eq_of_loc (h : w.Ray area d i j) (he : w.loc d i = w.loc d j) : i = j := by
  cases h with
  | self => rfl
  | go hi hl ht => have := ht.forward; rw [w.loc_step d hl] at this; omega

theorem Ray.reach (w : Board I n) (area : Set ℕ) (d : Bool) : ∀ i, w.place i ∈ area →
    ∃ j, w.Ray area d i j ∧ Round.Ends w area d j := by
  apply w.induct
  intro i ih hi
  by_cases hl : w.live i
  swap
  · exact ⟨i,.self,.inl ⟨hi,hl⟩⟩
  by_cases hj : w.place (w.step i d) ∈ area
  · obtain ⟨j,ht,he⟩ := ih hl d hj
    exact ⟨j,.go hi hl ht,he⟩
  · exact ⟨_,.go hi hl .self,.inr ⟨hj,w.shore_cross hl (fun he => hj (he.symm ▸ hi))⟩⟩

namespace Round

variable (r : w.Round)

def On (area : Set ℕ) (d : Bool) (i g : I) :=
  ∃ u, w.Ray area d i u ∧ w.place u ∈ area ∧ r.mark u d ∧ w.step u d = g

variable {r}

theorem On.info (h : r.On area d i g) : w.Shore d g ∧ w.place g ∈ area ∧
    w.Ray area d i g ∧ w.loc d i < w.loc d g := by
  obtain ⟨u,hr,hu,hm,rfl⟩ := h
  obtain ⟨hm,hl⟩ := r.middle _ _ hm
  obtain ⟨hg,he⟩ := w.middle_step hm hl d
  exact ⟨hg,he.symm ▸ hu,hr.join (.go hu hl .self),by rw [w.loc_step d hl]; exact Nat.lt_succ_of_le hr.forward⟩

theorem On.strict (h : r.On area d i g) (hi : w.Shore d i) : w.num d i < w.num d g := by
  have := h.info.2.2.2
  have := (w.shore_loc d i).mp hi
  unfold num; omega

theorem On.extend (h : r.On area d j g) (hr : w.Ray area d i j) : r.On area d i g := by
  obtain ⟨u,h,hu,hm,he⟩ := h
  exact ⟨u,hr.join h,hu,hm,he⟩

theorem On.later (h : r.On area d i g) (hr : w.Ray area d i j) (hj : w.num d j < w.num d g) :
    r.On area d j g := by
  obtain ⟨u,h,hu,hm,rfl⟩ := h
  refine ⟨u,hr.ordered h ?_,hu,hm,rfl⟩
  have := w.loc_step d (r.middle _ _ hm).2
  unfold num at hj; omega

theorem On.unique (h : r.On area d i j) (h' : r.On area d i k) (he : w.place j = w.place k) : j = k := by
  have he' := (w.same d j k).mpr he
  have := (w.shore_loc d j).mp h.info.1
  have := (w.shore_loc d k).mp h'.info.1
  have hh : w.loc d j = w.loc d k := by unfold num at he'; omega
  exact (h.info.2.2.1.ordered h'.info.2.2.1 hh.le).eq_of_loc hh

theorem Finer.on {q : w.Round} (h : q.Finer r) (hg : q.On area d i g) : r.On area d i g := by
  obtain ⟨u,hr,hu,hm,he⟩ := hg
  exact ⟨u,hr,hu,h.marks _ _ hm,he⟩

theorem trace (r : w.Round) (h : w.Ray area d i j) :
    ∃ path b, r.Trip area i j b path ∧ b + w.ahead d j = w.ahead d i ∧
      ∀ g ∈ path, r.On area d i g ∧ w.loc d g ≤ w.loc d j := by
  induction h with
  | self => exact ⟨[],0,.nil,zero_add _,by simp⟩
  | go hi hl ht ih =>
    obtain ⟨l,b,hb,he,hg⟩ := ih
    refine ⟨_,_,.go hi (r.basic hl d) le_rfl hb,by rw [add_assoc,he,w.ahead_step d hl],?_⟩
    intro g hm
    rcases List.mem_append.mp hm with hh | hh
    · obtain ⟨hc,rfl⟩ := r.charge_mem.mp hh
      exact ⟨⟨_,.self,hi,hc,rfl⟩,ht.forward⟩
    · exact ⟨(hg _ hh).1.extend (.go hi hl .self),(hg _ hh).2⟩

theorem spine (r : w.Round) (hi : w.place i ∈ area) (d : Bool) :
    ∃ l ∈ r.test area d (flat 1) i, ∀ g ∈ l, r.On area d i g := by
  obtain ⟨j,hj,he⟩ := Ray.reach w area d i hi
  obtain ⟨l,b,ht,hb,hg⟩ := r.trace hj
  exact ⟨l,⟨j,he,ht.more (le_self_add.trans (hb.le.trans (w.ahead_one d i)))⟩,fun g h => (hg g h).1⟩

theorem hits {s : Finset I} {b : Budget} (hi : w.place i ∈ area) (hb : flat 1 ≤ b)
    (hc : (r.test area d b i).Covers s) : ∃ g ∈ s, r.On area d i g := by
  obtain ⟨l,hl,hh⟩ := r.spine hi d
  obtain ⟨g,hg,hm⟩ := test_mono _ _ _ _ hb _ hc _ hl
  exact ⟨g,hm,hh _ hg⟩

theorem On.first {s t : Finset I} {b : Budget} (h : r.On area d i g) (hg : g ∈ t)
    (hb : flat 1 ≤ b) (hs : (r.paths area b i).Before s t) :
    ∃ j ∈ s, r.On area d i j ∧ w.num d j < w.num d g := by
  obtain ⟨u,hr,hu,hm,rfl⟩ := h
  obtain ⟨l,a,ht,he,hh⟩ := r.trace hr
  have hl := (r.middle _ _ hm).2
  have hf : a + atLayer (w.layer u) ≤ b := by
    rw [← w.ahead_step d hl,← add_assoc] at he
    exact le_self_add.trans (he.le.trans ((w.ahead_one d i).trans hb))
  have path := (ht.append (.step hu (r.basic hl d))).more hf
  simp only [charge,if_pos hm] at path
  obtain ⟨j,hj,hjs⟩ := hs l _ [] ⟨_,path⟩ hg
  obtain ⟨ho,hj'⟩ := hh _ hj
  refine ⟨j,hjs,ho,?_⟩
  have := (w.shore_loc d j).mp ho.info.1
  have := w.loc_step d hl
  unfold num; omega

end Round
end OAI.Geometry.Hirsch.Layer.Board
end

-- Endpoints
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I : Type} {n : ℕ} (w : Board I n) (d : Bool) (s : Finset I)

def left := sInf {z | ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = z}

theorem left_le {g : I} (hg : g ∈ s) (hh : w.Shore (!d) g) : w.left d s ≤ w.num d g :=
  Nat.sInf_le ⟨g,hg,hh,rfl⟩

namespace Round

variable {w} (r : w.Round) (area : Set ℕ) (i : I)

def Straddles := ∃ g ∈ s, r.On area d i g

def right := sInf {z | ∃ g ∈ s, r.On area d i g ∧ w.num d g = z}

variable {area d i s r} {t : Finset I} {H f : ℕ} {b : Budget}

theorem On.right_le {g : I} (ho : r.On area d i g) (hg : g ∈ s) :
    r.right d s area i ≤ w.num d g := Nat.sInf_le ⟨g,hg,ho,rfl⟩

theorem Straddles.endpoint (h : r.Straddles d s area i) :
    ∃ g ∈ s, r.On area d i g ∧ w.num d g = r.right d s area i := by
  obtain ⟨g,hg,ho⟩ := h
  exact Nat.sInf_mem (s := {z | ∃ g ∈ s, r.On area d i g ∧ w.num d g = z}) ⟨_,g,hg,ho,rfl⟩

theorem Straddles.greater (h : r.Straddles d s area i) (hi : w.Shore d i) :
    w.num d i < r.right d s area i := by
  obtain ⟨_,_,ho,he⟩ := h.endpoint
  exact he ▸ ho.strict hi

theorem west (hi : w.place i ∈ area) (hb : flat 1 ≤ b) (hc : (r.test area (!d) b i).Covers s) :
    w.left d s ≤ w.num d i ∧ ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = w.left d s := by
  obtain ⟨g,hg,ho⟩ := hits hi hb hc
  have hf := ho.info.2.2.1.forward
  have h₁ := w.reverse d i
  have h₂ := w.reverse d g
  have hh : w.num d g ≤ w.num d i := by unfold num at *; omega
  exact ⟨(w.left_le d s hg ho.info.1).trans hh,
    Nat.sInf_mem (s := {z | ∃ g ∈ s, w.Shore (!d) g ∧ w.num d g = z}) ⟨_,g,hg,ho.info.1,rfl⟩⟩

theorem falls_test (r : w.Round) (area : Set ℕ) (d : Bool) (b : Budget) :
    Trial.Falls w.rank (r.test area d b) := by
  rintro g path ⟨_,_,ht⟩ j hj
  exact (ht.member hj).2

theorem keys_inside (hc : (r.test area d b i).Covers s) (hm : (r.test area d b i).Minimal s)
    {g : I} (hg : g ∈ s) : w.place g ∈ area := by
  obtain ⟨l,t,⟨_,_,ht⟩,_⟩ := hm.essential hc hg
  exact (ht.member (by simp : g ∈ l ++ g :: t)).1

def core (r : w.Round) (area : Set ℕ) (d : Bool) (H f : ℕ) (i : I)
    (hi : w.place i ∈ area) (hH : 1 ≤ H) (hf : 2*H ≤ f) : Trial.Core w.rank where
  short := r.test area (!d) (flat H) i
  long := r.test area (!d) (flat f) i
  paths := r.paths area (flat H) i
  near := r.test area (!d) (flat H)
  far := r.test area (!d) (flat (f-H))
  inhabited := by
    obtain ⟨l,⟨j,hj,ht⟩,_⟩ := r.spine hi (!d)
    exact ⟨l,j,hj,ht.more (fun _ => hH)⟩
  includes := fun _ ⟨j,_,ht⟩ => ⟨j,ht⟩
  refines := test_mono _ _ _ _ (fun _ => by simp only [flat]; omega)
  transfer := transfers _ (fun _ => by simp only [Pi.add_apply,flat]; omega)
  nested := fun _ => test_mono _ _ _ _ (fun _ => by simp only [flat]; omega)
  falls := r.falls_test area (!d) (flat H)

variable {hi : w.place i ∈ area} {hH : 1 ≤ H} {hf : 2*H ≤ f}

theorem newer_left (hc : (r.core area d H f i hi hH hf).Cut s)
    (hn : (r.core area d H f i hi hH hf).Newer s t) : w.left d t < w.left d s := by
  have hh := (r.core area d H f i hi hH hf).refines _ hc.1
  obtain ⟨_,g,hg,hw,he⟩ := west hi (fun _ => hH) hh
  have inside := keys_inside hh hc.2 hg
  obtain ⟨j,hj,ho⟩ := hits inside (fun _ => show 1 ≤ f-H by omega) (hn.2.2 g hg).1
  have := ho.strict hw
  have := w.reverse d j
  have := w.reverse d g
  have := w.left_le d t hj ho.info.1
  omega

theorem newer_right (hn : (r.core area d H f i hi hH hf).Newer s t)
    (ht : r.Straddles d t area i) : r.right d s area i < r.right d t area i := by
  obtain ⟨g,hg,ho,he⟩ := ht.endpoint
  obtain ⟨j,hj,hh,hle⟩ := ho.first hg (fun _ => hH) hn.2.1
  exact (hh.right_le hj).trans_lt (hle.trans_eq he)

structure Links (r : w.Round) (d : Bool) (P : I → Prop) : Prop where
  east : ∀ i, r.mark i d → P (w.step i d)
  west : ∀ i, r.mark i (!d) →
    ∃ j, (j = i ∨ r.jump i (!d) j) ∧ w.Middle j ∧ w.live j ∧ P (w.step j d)

theorem Links.divert {P : I → Prop} (h : r.Links d P) {g j : I} {pre rest : List I}
    (ht : r.Trip area i j b (pre ++ g :: rest)) (hw : w.Shore (!d) g) :
    ∃ y l, P y ∧ w.Shore d y ∧ w.place y = w.place g ∧
      r.Trip area i y (b+flat 1) l ∧ l ⊆ pre ++ [g,y] := by
  obtain ⟨u,e,a,hpre,hu,hm,he,hb⟩ := ht.split rfl
  have med := r.middle _ _ hm
  have info := w.middle_step med.1 med.2 e
  have eq := w.shore_inj (he ▸ info.1) hw
  subst e
  obtain ⟨v,hv,hmed,hl,hp⟩ := h.west u hm
  have heq : w.layer v = w.layer u := hv.elim (fun e => by rw [e]) (fun h => (r.localJump _ _ _ h).2.1)
  have place : w.place v = w.place u := congrArg (· / 3) heq
  have pref : ∃ l, r.Trip area i v b l ∧ l ⊆ pre ++ [g] := by
    rcases hv with rfl | hj
    · exact ⟨pre,hpre.more (le_self_add.trans hb),fun _ hh => List.mem_append_left _ hh⟩
    · have hh := (hpre.append (.step hu ⟨med.2,.inr hj⟩)).more hb
      rw [charge,if_pos hm,he] at hh
      exact ⟨_,hh,fun _ h => h⟩
  obtain ⟨l,ht',hs⟩ := pref
  have hy := w.middle_step hmed hl d
  have tail := Trip.step (place.symm ▸ hu) (r.basic hl d)
  refine ⟨_,_,hp,hy.1,hy.2.trans (place.trans (he ▸ info.2.symm)),ht'.append (tail.more ?_),?_⟩
  · intro x; simp only [atLayer,flat]; split <;> omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hs hx; simp_all only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]; tauto
    · simp [(r.charge_mem.mp hx).2]

end Round
end OAI.Geometry.Hirsch.Layer.Board
end

-- Ledger
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} (gate : Trial.Gates pins w.place K gamma alpha)

structure Depths (K : ℕ) where
  step : ℕ
  pos : 1 ≤ step

namespace Depths

variable (D : Depths K)

def low := (K+2)*D.step
def near := D.low+1
def limit := (3*K+6)*D.near
def band := D.limit + (K+2)*D.step
def max := D.band+1+(K+2)*D.step

theorem order : D.step ≤ D.low ∧ 1 ≤ D.near ∧ 4*D.near ≤ D.limit ∧ D.limit ≤ D.band ∧ D.band < D.max := by
  have h := Nat.mul_le_mul_right D.step (by omega : 1 ≤ K+2)
  have h' := Nat.mul_le_mul_right D.near (by omega : 4 ≤ 3*K+6)
  simp only [low,near,limit,band,max] at *
  omega

end Depths

structure Ledger (old : w.Round) (area : Set ℕ) (d : Bool) (D : Depths K) (M A : ℝ) : Prop where
  link : 0 ≤ A
  mass : 0 ≤ M
  available : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
    ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g
  bounds : ∀ r : w.Round, r.Finer old → ∀ i, w.place i ∈ area → ∀ a b : Budget,
    a ≤ flat D.max → a + flat D.step ≤ b →
    gate.Bounds (gate.cuts (r.test area (!d) a i) (r.test area (!d) b i)) M A

namespace Ledger

variable {gate} {old r q : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}

def tests (hr : r.Finer old) (i : I) (a b : Budget) (he : a ≤ flat D.max) (hb : a + flat D.step ≤ b) :
    Trial.Tests w.place D.max D.step :=
  { r.tests area (!d) i a b _ _ he hb with
    next := fun g => if w.place g ∈ area then old.test area (!d) (flat D.step) g else {[]}
    transfer := by
      rintro pre g rest ⟨j,_,ht⟩ s hc hn hg
      have hi := (ht.member (by simp : g ∈ pre ++ g :: rest)).1
      simp only [if_pos hi]
      exact hr.test le_rfl _ (Round.transfers _ hb pre g rest ⟨j,ht⟩ s hc hn hg)
    nextBound := by
      intro g
      split
      · exact fun l ⟨_,_,ht⟩ x => ht.bound x
      · rintro l rfl x; simp [Trial.keysAt] }

omit [Fintype I] in
theorem serves (hr : r.Finer old) (i : I) (a b : Budget) (he : a ≤ flat D.max) (hb : a + flat D.step ≤ b)
    (hav : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
      ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g) :
    gate.Serves (tests (area := area) (d := d) hr i a b he hb) := by
  intro x g hh
  simp only [tests]
  split
  · exact hav x g ‹_› hh
  · exact ⟨[],rfl,by simp⟩

theorem make {U : ℝ} (hg : 0 < gamma) (ha : 0 ≤ alpha) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (change : ∀ z, Nonempty (gate.Resample z))
    (hm : (Trial.Tests.capacity K D.max D.step : ℝ)*U ≤ gamma*M)
    (hl : (Trial.Tests.capacity K D.max D.step : ℝ)*(alpha+(K*D.max+D.step+1)*pins.rate) ≤ gamma*A)
    (hav : ∀ x g, w.place g ∈ area → ¬gate.bad g x →
      ∃ l ∈ old.test area (!d) (flat D.step) g, ∀ j ∈ l, j ∈ gate.pass x → w.place j = w.place g)
    (cap : ∀ i, w.place i ∈ area → p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (gate.pass x)) ≤ U) :
    Ledger gate old area d D M A := by
  refine ⟨hA,hM,hav,fun r hr i hi a b he hb => ?_⟩
  apply Trial.Gates.bounds (serves hr i a b he hb hav) hg ha change _ hm hl
  exact (p.mono fun x h => hr.test (le_add_self.trans hb) _ h).trans (cap i hi)

variable (L : Ledger gate old area d D M A) {i : I} {f : ℕ} {b : Budget} {s : Finset I}

def book (_L : Ledger gate old area d D M A) (r : w.Round) (i : I) (b : Budget) :=
  gate.cuts (r.test area (!d) (flat D.near) i) (r.test area (!d) b i)

theorem mem : s ∈ L.book r i b ↔ s.card ≤ K ∧ (r.test area (!d) b i).Covers s ∧
    (r.test area (!d) (flat D.near) i).Minimal s ∧ gate.Possible s := gate.mem_cuts

theorem sub {a : Budget} (h : a ≤ b) : L.book r i b ⊆ L.book r i a := by
  intro s hs
  obtain ⟨hk,hc,hm,hp⟩ := L.mem.mp hs
  exact L.mem.mpr ⟨hk,Round.test_mono _ _ _ _ h _ hc,hm,hp⟩

def loss (_L : Ledger gate old area d D M A) := (K+1)*A*M
def key (_L : Ledger gate old area d D M A) := (1+A)*pins.rate
def beta := 2*M * (K*(L.key+L.loss))

theorem positive : 0 ≤ L.loss ∧ 0 ≤ L.key ∧ 0 ≤ L.beta := by
  have := L.link
  have := L.mass
  have := pins.pos
  unfold beta key loss
  constructor
  · positivity
  constructor <;> positivity

theorem bound (hr : r.Finer old) (hi : w.place i ∈ area) (hb : flat (2*D.near) ≤ b) :
    gate.Bounds (L.book r i b) M A := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := D.order
  apply L.bounds r hr i hi
  · exact fun _ => show D.near ≤ D.max by omega
  · apply le_trans _ hb
    intro x; simp only [Pi.add_apply,flat,Depths.near]; omega

theorem discard {B : Finset (Finset I)} (hb : gate.Bounds B M A) (hr : r.Finer old)
    (hi : w.place i ∈ area) (hf : D.low ≤ f) :
    pins.mass (B.filter fun t => ¬(r.test area (!d) (flat f) i).Minimal t) ≤ L.loss := by
  let paths := fun j => r.test area (!d) (flat ((j+1)*D.step)) i
  apply le_trans _ (hb.loss L.link paths (by
    intro j hj
    apply Trial.Gates.Bounds.mass (L.bounds r hr i hi _ _ ?_ ?_)
    · have := Nat.mul_le_mul_right D.step (by omega : j+1 ≤ K+2)
      exact fun _ => show (j+1)*D.step ≤ D.max by unfold Depths.max; omega
    · intro x; simp only [Pi.add_apply,flat,add_mul,one_mul]; omega))
  apply pins.mass_mono
  intro s hs
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hs
  exact Finset.mem_filter.mpr ⟨hs,fun hm => hn fun t ht hc =>
    hm _ ht (Round.test_mono _ _ _ _ (fun _ => hf) _ hc)⟩

def core (_L : Ledger gate old area d D M A) (r : w.Round) (hi : w.place i ∈ area)
    (hf : 2*D.near ≤ f) := r.core area d D.near f i hi D.order.2.1 hf

theorem cut (hi : w.place i ∈ area) (hf : 2*D.near ≤ f) (hs : s ∈ L.book r i (flat f)) :
    (L.core r hi hf).Cut s := ⟨(L.mem.mp hs).2.1,(L.mem.mp hs).2.2.1⟩

theorem bad (hr : r.Finer old) (hi : w.place i ∈ area) (hf : 2*D.near ≤ f)
    {B C : Finset (Finset I)} (hB : B ⊆ L.book r i (flat f)) (hC : C ⊆ L.book r i (flat f)) :
    pins.pairMass B C (fun s t => ¬(L.core r hi hf).Good s t) ≤ L.beta := by
  let c := L.core r hi hf
  let list := L.book r i (flat f)
  have hb := L.bound hr hi (show flat (2*D.near) ≤ flat f from fun _ => hf)
  have hs : ∀ s ∈ list, ∀ g ∈ s, w.place g ∈ area := fun _ h _ hg =>
    Round.keys_inside (c.refines _ (L.cut hi hf h).1) (L.cut hi hf h).2 hg
  have hbad := c.bad_pairs pins list L.positive.2.1 L.positive.1
    (fun _ h => (L.mem.mp h).1) hb.key
    (fun g hg => L.discard hb hr (by obtain ⟨s,h,hg⟩ := hg; exact hs s h g hg) (Nat.le_succ _))
  refine ((pins.pair_mono hB hC (fun _ _ _ _ h => h)).trans hbad).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb.mass (by norm_num))
    (mul_nonneg (by positivity) (add_nonneg L.positive.2.1 L.positive.1))

end Ledger
end OAI.Geometry.Hirsch.Layer.Board
end

-- Switch
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I}

theorem Pins.split_mass (pins : Pins p I) (B : Finset (Finset I)) (P : Finset I → Prop) [DecidablePred P] :
    pins.mass B ≤ pins.mass (B.filter P) + pins.mass (B.filter fun s => ¬P s) := by
  apply le_trans _ (pins.mass_union ..)
  apply pins.mass_mono
  intro s hs; simp [hs]; tauto

theorem Pins.retain (pins : Pins p I) {B C : Finset (Finset I)} (P : Finset I → Prop) [DecidablePred P]
    {loss : ℝ} (sub : B ⊆ C) (hb : pins.mass (C.filter fun s => ¬P s) ≤ loss) :
    pins.mass B ≤ pins.mass (B.filter P) + loss :=
  (pins.split_mass B P).trans (add_le_add_right ((pins.mass_mono (Finset.filter_subset_filter _ sub)).trans hb) _)

namespace Board.Ledger

variable [Fintype I] {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i y : I} {s t : Finset I} {f scale : ℕ}

def close (i : I) (scale : ℕ) := (L.book old i (flat (4*D.near))).filter fun t =>
  ∃ g ∈ t, old.On area d i g ∧ w.left d t + scale ≤ w.num d g ∧ 4*w.num d g ≤ 4*w.num d i + scale

theorem force_charge (hr : r.Finer old) (hi : w.place i ∈ area) (hscale : 0 < scale)
    (ht : t ∈ L.book r i (flat (4*D.near))) (ht' : t ∈ L.book old i (flat (4*D.near)))
    (hs : s ∈ L.close i scale) (hleft : 4*w.num d i ≤ 4*w.left d t + scale)
    (hg : (L.core old hi (by omega : 2*D.near ≤ 4*D.near)).Good t s) :
    r.Straddles d t area i ∧ 4*r.right d t area i ≤ 4*w.num d i + scale := by
  obtain ⟨hs,g,hgs,ho,h₁,h₂⟩ := Finset.mem_filter.mp hs
  have hH := D.order.2.1
  have hf : 2*D.near ≤ 4*D.near := by omega
  let c := L.core old hi hf
  have newer : c.Newer t s := by
    rcases hg.order (L.cut hi hf ht') (L.cut hi hf hs) with hh | hh
    · exact hh
    · have := Round.newer_left (L.cut hi hf hs) hh
      omega
  obtain ⟨l,b,hp,hb,hh⟩ := r.trace ho.info.2.2.1
  have hit : Trial.Hit t l := by
    by_contra miss
    have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d i))
    have cost : b + flat D.near ≤ flat (4*D.near) := by
      intro x; have := small x; simp only [flat,Pi.add_apply] at *; omega
    have cover := hr.test le_rfl _ (hp.carry miss (L.mem.mp ht).2.1 cost)
    obtain ⟨j,hj⟩ := (c.refines _ (L.cut hi hf ht').1).nonempty c.inhabited
    exact (c.falls.older cover (hg.2.2 g hgs) j hj).not_gt ((newer.2.2 j hj).2 g hgs)
  obtain ⟨j,hj,hjt⟩ := hit
  obtain ⟨ho',hle⟩ := hh j hj
  have hnum : w.num d j ≤ w.num d g := Nat.div_le_div_right hle
  have := ho'.right_le hjt
  exact ⟨⟨j,hjt,ho'⟩,by omega⟩

def Cohort (_L : Ledger gate old area d D M A) (r : w.Round) (i : I) (scale : ℕ) (B : Finset (Finset I)) :=
  (∀ s ∈ B, r.Straddles d s area i ∧ w.left d s + scale ≤ r.right d s area i) ∧
  ∀ s ∈ B, ∀ t ∈ B, 4*w.left d s ≤ 4*w.left d t + scale ∧
    4*r.right d t area i ≤ 4*r.right d s area i + scale

set_option maxHeartbeats 600000 in
theorem shift (hr : r.Finer old) (hi : w.place i ∈ area) (hf : 9*D.near ≤ f)
    {B : Finset (Finset I)} (hB : B ⊆ L.book r i (flat f)) (hc : L.Cohort r i scale B)
    (hscale : 0 < scale) {theta : ℝ} (hth : 0 < theta) (hbeta : 3*L.beta < theta^2)
    (hm : 3*(theta+L.loss) ≤ pins.mass B)
    {P : I → Prop} (link : r.Links d P)
    (stable : ∀ u y, w.place u ∈ area → w.place y ∈ area → P u → P y → theta ≤ pins.mass (L.close u scale) → theta ≤ pins.mass (L.close y scale)) :
    ∃ y C, w.place y ∈ area ∧ w.Shore d y ∧ C ⊆ B ∧ C ⊆ L.book r y (flat (f-3*D.near)) ∧
      pins.mass B / 3 ≤ pins.mass C + L.key + L.loss + theta ∧
      ∀ t ∈ C, r.Straddles d t area y ∧ r.right d t area y < r.right d t area i := by
  have hH := D.order.2.1
  have hf' : 2*D.near ≤ f := by omega
  let c := L.core r hi hf'
  have bound := L.bound hr hi (show flat (2*D.near) ≤ flat f from fun _ => hf')
  have big : 3*L.beta < (pins.mass B)^2 := by nlinarith [L.positive.1]
  obtain ⟨s,hs,hheavy⟩ := (c.heavy pins B (fun t ht => L.cut hi hf' (hB ht)) (L.bad hr hi hf' hB hB) big).1
  let older := B.filter (c.Newer s)
  change pins.mass B / 3 < pins.mass older at hheavy
  have sub : older ⊆ L.book r i (flat f) := (Finset.filter_subset ..).trans hB
  have sc := L.cut hi hf' (hB hs)
  obtain ⟨u,hus,hu,heu⟩ := (hc.1 s hs).1.endpoint
  have pu : P u := by
    obtain ⟨v,_,_,hv,he⟩ := hu
    exact he ▸ link.east _ hv
  let keep := fun j t => (old.test area (!d) (flat D.near) j).Minimal t
  have loss : ∀ j, w.place j ∈ area → pins.mass ((L.book r i (flat f)).filter fun t => ¬keep j t) ≤ L.loss :=
    fun _ hj => L.discard bound (.refl old) hj (Nat.le_succ _)
  have east : theta ≤ pins.mass (L.close u scale) := by
    have err := pins.retain (keep u) sub (loss u hu.info.2.1)
    have incl : older.filter (keep u) ⊆ L.close u scale := by
      intro t ht
      obtain ⟨ht,hm⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht,hn⟩ := Finset.mem_filter.mp ht
      obtain ⟨hk,_,_,hp⟩ := L.mem.mp (hB ht)
      have cov := hr.test (show flat (4*D.near) ≤ flat (f-D.near) from fun _ => by simp only [flat]; omega)
        _ (hn.2.2 u hus).1
      obtain ⟨g,hg,ho,he⟩ := (hc.1 t ht).1.endpoint
      have hlt := Round.newer_right hn (hc.1 t ht).1
      have ho' := hr.on (ho.later hu.info.2.2.1 (by omega))
      have h₁ := (hc.1 t ht).2
      have h₂ := (hc.2 s hs t ht).2
      exact Finset.mem_filter.mpr ⟨L.mem.mpr ⟨hk,cov,hm,hp⟩,g,hg,ho',by omega,by omega⟩
    linarith [pins.mass_mono incl]
  have sh := c.refines _ sc.1
  obtain ⟨_,g,hgs,hgw,heg⟩ := Round.west hi (fun _ => hH) sh
  obtain ⟨pre,rest,hh,hn⟩ := sc.2.essential sh hgs
  obtain ⟨j,_,htrip⟩ := hh
  obtain ⟨y,l,py,hy,he,hpath,hl⟩ := link.divert htrip hgw
  have hey : w.num d y = w.left d s := ((w.same d y g).mpr he).trans heg
  have hyi := he.symm ▸ Round.keys_inside sh sc.2 hgs
  have hybit := stable u y hu.info.2.1 hyi pu py east
  let free := older.filter (y ∉ ·)
  let both := free.filter (keep y)
  have hfree : free ⊆ older := Finset.filter_subset ..
  have hboth : both ⊆ free := Finset.filter_subset ..
  have err₁ : pins.mass older ≤ pins.mass free + L.key := by
    apply pins.retain (fun t => y ∉ t) sub
    simpa only [not_not,key] using bound.key y
  have err₂ := pins.retain (keep y) (hfree.trans sub) (loss y hyi)
  change pins.mass free ≤ pins.mass both + L.loss at err₂
  have moved : ∀ t ∈ both, t ∈ L.book r y (flat (f-3*D.near)) ∧ t ∈ L.book old y (flat (4*D.near)) := by
    intro t h
    obtain ⟨ht,hm⟩ := Finset.mem_filter.mp h
    obtain ⟨ht,hyt⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hnew⟩ := Finset.mem_filter.mp ht
    obtain ⟨hk,hcov,_,hp⟩ := L.mem.mp (hB ht)
    have miss := hnew.2.1.missed ⟨j,htrip⟩ hn
    have avoid : ¬Trial.Hit t l := by
      rintro ⟨v,hv,hvt⟩
      rcases List.mem_append.mp (hl hv) with hv | hv
      · exact miss ⟨v,hv,hvt⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl
        · exact Finset.disjoint_left.mp hnew.1.1 hgs hvt
        · exact hyt hvt
    have cost : flat D.near + flat 1 + flat (f-3*D.near) ≤ flat f :=
      fun _ => by simp only [flat,Pi.add_apply]; omega
    have cov := hpath.carry avoid hcov cost
    exact ⟨L.mem.mpr ⟨hk,cov,fun a ha hh => hm _ ha (hr.test le_rfl _ hh),hp⟩,
      L.mem.mpr ⟨hk,hr.test (fun _ => by simp only [flat]; omega) _ cov,hm,hp⟩⟩
  let c' := L.core old hyi (by omega : 2*D.near ≤ 4*D.near)
  let good := fun t => ∃ a ∈ L.close y scale, c'.Good t a
  let C := both.filter good
  have err₃ : pins.mass both ≤ pins.mass C + theta := by
    apply pins.retain good Finset.Subset.rfl
    have hb := L.bad (.refl old) hyi (by omega : 2*D.near ≤ 4*D.near)
      (fun _ h => (moved _ h).2) (show L.close y scale ⊆ _ from Finset.filter_subset ..)
    have hexc := (pins.pair_exception (P := fun t a => ¬c'.Good t a) both (L.close y scale)).trans hb
    have hhx : pins.mass (both.filter fun t => ¬good t) * pins.mass (L.close y scale) ≤ L.beta := by
      apply le_trans _ hexc
      apply mul_le_mul_of_nonneg_right _ (pins.mass_nonneg _)
      apply pins.mass_mono
      intro t ht
      simpa [good] using ht
    by_contra! hh
    have hh' := mul_lt_mul_of_pos_right hh hth
    have hh'' := mul_le_mul_of_nonneg_left hybit (le_trans hth.le hh.le)
    have low := (hh'.trans_le hh'').trans_le hhx

    nlinarith only [low,hbeta,L.positive.2.2]
  have sub' : C ⊆ older := (Finset.filter_subset ..).trans (hboth.trans hfree)
  refine ⟨y,C,hyi,hy,sub'.trans (Finset.filter_subset ..),fun _ h => (moved _ (Finset.mem_filter.mp h).1).1,
    by linarith,?_⟩
  intro t ht
  obtain ⟨ht',hnew⟩ := Finset.mem_filter.mp (sub' ht)
  obtain ⟨ht,a,ha,hg⟩ := Finset.mem_filter.mp ht
  obtain ⟨hm,ho⟩ := moved t ht
  have hleft := (hc.2 s hs t ht').1
  obtain ⟨hh,hnear⟩ := L.force_charge hr hyi hscale (L.sub (fun _ => by simp only [flat]; omega) hm) ho ha (by omega) hg
  have hlt := Round.newer_right hnew (hc.1 t ht').1
  have hgap := (hc.1 s hs).2
  exact ⟨hh,by omega⟩

end Board.Ledger
end OAI.Geometry.Hirsch.Layer
end

-- Straddlers
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Ledger

theorem scale_exists {a x h : ℕ} (hx : 0 < x) (hb : x < a^h) :
    ∃ j : Fin h, a^j.val ≤ x ∧ x < a*a^j.val := by
  induction h with
  | zero => simp at hb; omega
  | succ h ih =>
    by_cases he : x < a^h
    · obtain ⟨j,hj⟩ := ih he
      exact ⟨j.castSucc,hj⟩
    · exact ⟨Fin.last h,Nat.le_of_not_gt he,by simpa [pow_succ'] using hb⟩

abbrev Box (a h : ℕ) := Fin h × Fin (4*a) × Fin (4*a)

def Box.fits {a h : ℕ} (box : Box a h) (l v r : ℕ) :=
  let s := a^box.1.val
  l+s ≤ r ∧
  4*l + box.2.1.val*s ≤ 4*v ∧ 4*v ≤ 4*l + box.2.1.val*s+s ∧
  4*v + box.2.2.val*s ≤ 4*r ∧ 4*r ≤ 4*v + box.2.2.val*s+s

theorem Box.exists_fits {a h l v r : ℕ} (ha : 0 < a) (hl : l ≤ v) (hr : v < r) (hn : r < a^h) :
    ∃ box : Box a h, box.fits l v r := by
  obtain ⟨j,hj,he⟩ := scale_exists (a := a) (h := h) (x := r-l) (by omega) (by omega)
  let s := a^j.val
  have hs : 0 < s := pow_pos ha _
  have choose : ∀ k ≤ r-l, ∃ z : Fin (4*a), z.val*s ≤ 4*k ∧ 4*k ≤ z.val*s+s := by
    intro k hk
    have small : 4*k < (4*a)*s := by rw [mul_assoc]; change r-l < a*s at he; omega
    have hb := Nat.div_mul_le_self (4*k) s
    have hmod := Nat.mod_lt (4*k) hs
    have hid := Nat.mod_add_div (4*k) s
    rw [mul_comm s] at hid
    exact ⟨⟨4*k/s,(Nat.div_lt_iff_lt_mul hs).mpr small⟩,hb,by dsimp; omega⟩
  obtain ⟨p,hp,hp'⟩ := choose (v-l) (by omega)
  obtain ⟨q,hq,hq'⟩ := choose (r-v) (by omega)
  refine ⟨(j,p,q),?_⟩
  dsimp only [fits,s] at *
  omega

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A)

def colors (a h : ℕ) (theta : ℝ) (i : I) (j : Fin h) : Bool :=
  decide (theta ≤ pins.mass (L.close i (a^j.val)))

def factor (a h : ℕ) : ℝ := 1 + 9*Fintype.card (Box a h)

def remaining (r : w.Round) (area : Set ℕ) (d : Bool) (i : I) (s : Finset I) :=
  s.filter fun g => w.num d g ≤ r.right d s area i

omit [Fintype I] in
theorem drops {i y : I} {s : Finset I} (hs : r.Straddles d s area i)
    (h : r.right d s area y < r.right d s area i) :
    (remaining r area d y s).card < (remaining r area d i s).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    obtain ⟨hg,hg'⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨hg,hg'.trans h.le⟩
  · intro he
    obtain ⟨g,hg,_,he'⟩ := hs.endpoint
    have hh : g ∈ remaining r area d i s := Finset.mem_filter.mpr ⟨hg,he'.le⟩
    rw [← he] at hh
    exact h.not_ge (he' ▸ (Finset.mem_filter.mp hh).2)

theorem straddlers (hr : r.Finer old) {a h : ℕ} (ha : 0 < a) (hn : n ≤ a^h)
    {theta : ℝ} (hth : 0 < theta) (hbeta : 3*L.beta < theta^2) (herr : L.key+L.loss ≤ theta)
    {color : Fin h → Bool} (link : r.Links d (fun u => w.place u ∈ area → L.colors a h theta u = color))
    {i : I} (hi : w.place i ∈ area) (he : w.Shore d i) :
    pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ factor a h ^ K * theta := by
  have hF : 1 ≤ factor a h := by unfold factor; exact le_add_of_nonneg_right (by positivity)
  have aux : ∀ k i, w.place i ∈ area → w.Shore d i → ∀ B ⊆ L.book r i (flat ((3*k+6)*D.near)),
      (∀ s ∈ B, r.Straddles d s area i ∧ (remaining r area d i s).card ≤ k) →
      pins.mass B ≤ factor a h ^ k * theta := by
    intro k
    induction k with
    | zero =>
      intro i _ _ B _ hB
      have empty : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro s hs
        obtain ⟨hs,hk⟩ := hB s hs
        obtain ⟨g,hg,_,he⟩ := hs.endpoint
        have hh : (remaining r area d i s).Nonempty := ⟨g,Finset.mem_filter.mpr ⟨hg,he.le⟩⟩
        exact hh.card_pos.not_ge hk)
      simp [empty,Pins.mass,hth.le]
    | succ k ih =>
      intro i hi he B hB hb
      let f := (3*(k+1)+6)*D.near
      have hf : 9*D.near ≤ f := Nat.mul_le_mul_right _ (by omega)
      have heq : f-3*D.near = (3*k+6)*D.near := by
        have : f = (3*k+6)*D.near + 3*D.near := by unfold f; ring
        omega
      let group := fun box : Box a h => B.filter fun s => box.fits (w.left d s) (w.num d i) (r.right d s area i)
      have split : pins.mass B ≤ ∑ box, pins.mass (group box) := by
        apply pins.mass_cover
        intro s hs
        have cov := (L.mem.mp (hB hs)).2.1
        have h₁ := (Round.west hi (show flat 1 ≤ flat f from fun _ => by
          have := D.order.2.1; simp only [flat]; omega) cov).1
        have h₂ := (hb _ hs).1.greater he
        obtain ⟨g,_,_,hg⟩ := (hb _ hs).1.endpoint
        obtain ⟨box,hbox⟩ := Box.exists_fits ha h₁ h₂ (hg ▸ (w.num_lt d g).trans_le hn)
        exact ⟨box,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hs,hbox⟩⟩
      have low : theta ≤ factor a h^k * theta := le_mul_of_one_le_left hth.le (one_le_pow₀ hF)
      have each : ∀ box : Box a h, pins.mass (group box) ≤ 9*(factor a h^k*theta) := by
        intro box
        let scale := a^box.1.val
        have sub : group box ⊆ B := Finset.filter_subset ..
        have hc : L.Cohort r i scale (group box) := by
          refine ⟨fun s hs => ⟨(hb _ (sub hs)).1,(Finset.mem_filter.mp hs).2.1⟩,?_⟩
          intro s hs t ht
          have lhs := (Finset.mem_filter.mp hs).2
          have rhs := (Finset.mem_filter.mp ht).2
          unfold Box.fits at lhs rhs
          dsimp only [scale] at *
          omega
        by_cases hm : 3*(theta+L.loss) ≤ pins.mass (group box)
        swap
        · linarith [L.positive.2.1]
        obtain ⟨y,C,hy,hey,hsub,hcov,hkeep,hdrop⟩ :=
          L.shift hr hi hf (sub.trans hB) hc (pow_pos ha _) hth hbeta hm link (by
            intro u y hui hyi hu hy
            have eq := congrFun ((hu hui).trans (hy hyi).symm) box.1
            intro hu'
            have he : L.colors a h theta u box.1 = true := decide_eq_true hu'
            exact of_decide_eq_true (eq.symm.trans he))
        rw [heq] at hcov
        have high := ih y hy hey C hcov (by
          intro s hs
          obtain ⟨hold,hk⟩ := hb _ (sub (hsub hs))
          obtain ⟨hnew,hlt⟩ := hdrop _ hs
          exact ⟨hnew,Nat.lt_succ_iff.mp ((drops hold hlt).trans_le hk)⟩)
        linarith
      calc
        _ ≤ ∑ box, pins.mass (group box) := split
        _ ≤ ∑ _ : Box a h, 9*(factor a h^k*theta) := Finset.sum_le_sum fun b _ => each b
        _ ≤ _ := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_succ]
          have he : factor a h = 1 + 9*Fintype.card (Box a h) := rfl
          calc
            _ ≤ (factor a h)*(factor a h^k*theta) := by
              rw [← mul_assoc]; gcongr; linarith
            _ = _ := by ring
  apply aux K i hi he _ (Finset.filter_subset ..)
  intro s hs
  obtain ⟨hs,hstr⟩ := Finset.mem_filter.mp hs
  exact ⟨hstr,(Finset.card_filter_le ..).trans (L.mem.mp hs).1⟩

end OAI.Geometry.Hirsch.Layer.Board.Ledger
end

-- Bands
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i j : I} {s : Finset I}

theorem Ray.last (hi : w.place i ∈ area) :
    ∃ j, w.place j ∈ area ∧ w.Ray area d i j ∧
      ∀ g, w.place g ∈ area → w.Ray area d i g → w.Ray area d g j := by
  let keys := Finset.univ.filter fun g => w.place g ∈ area ∧ w.Ray area d i g
  have ne : keys.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,.self⟩⟩
  obtain ⟨j,hj,hm⟩ := keys.exists_max_image (w.loc d) ne
  obtain ⟨_,hj,hr⟩ := Finset.mem_filter.mp hj
  exact ⟨j,hj,hr,fun g hg ht => ht.ordered hr (hm _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg,ht⟩))⟩

omit [Fintype I] in
theorem Round.missed_ray (hr : w.Ray area d i j) (hn : ¬r.Straddles d s area i) :
    ∃ path b, r.Trip area i j b path ∧ b + w.ahead d j = w.ahead d i ∧ ¬Trial.Hit s path := by
  obtain ⟨l,b,ht,hb,hh⟩ := r.trace hr
  exact ⟨l,b,ht,hb,fun ⟨g,hg,hm⟩ => hn ⟨g,hm,(hh _ hg).1⟩⟩

namespace Ledger

def depth (_L : Ledger gate old area d D M A) (i : I) := flat D.band + w.ahead d i

def band (r : w.Round) (i : I) := L.book r i (L.depth i)

theorem range_depth (i : I) : flat D.band ≤ L.depth i ∧ L.depth i ≤ flat (D.band+1) :=
  ⟨le_self_add,fun _ => Nat.add_le_add_left (w.ahead_one d i _) _⟩

theorem base : 2*D.near ≤ D.limit := by have := D.order; omega

theorem band_sub : L.band r i ⊆ L.book r i (flat D.limit) :=
  L.sub ((show flat D.limit ≤ flat D.band from fun _ => D.order.2.2.2.1).trans (L.range_depth i).1)

theorem persists (hs : s ∈ L.band r i) (hn : ¬r.Straddles d s area i)
    (hm : (r.test area (!d) (flat D.low) j).Minimal s) {g : I}
    (hg : w.Ray area d i g) (hj : w.Ray area d g j) : s ∈ L.band r g := by
  obtain ⟨hk,hc,_,hp⟩ := L.mem.mp hs
  obtain ⟨l,b,ht,hb,hmiss⟩ := Round.missed_ray hg hn
  have cost : b + L.depth g ≤ L.depth i := by unfold depth; rw [add_left_comm,hb]
  refine L.mem.mpr ⟨hk,ht.carry hmiss hc cost,fun t hts hc => ?_,hp⟩
  have miss : ¬r.Straddles d t area g := fun ⟨v,hv,ho⟩ => hn ⟨v,hts.subset hv,ho.extend hg⟩
  obtain ⟨l,b,ht,hb,hmiss⟩ := Round.missed_ray hj miss
  apply hm t hts
  apply ht.carry hmiss hc
  have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d g))
  intro x; have := small x
  simp only [Pi.add_apply,flat,Depths.near] at *; omega

theorem common (hr : r.Finer old) (hi : w.place i ∈ area) {err : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err) :
    ∃ B ⊆ L.band r i, pins.mass (L.band r i) ≤ pins.mass B + err + L.loss ∧
      ∀ g, w.place g ∈ area → w.Ray area d i g → B ⊆ L.band r g := by
  obtain ⟨j,hj,hij,hh⟩ := Ray.last (d := d) hi
  let free := (L.band r i).filter fun s => ¬r.Straddles d s area i
  let keep := (r.test area (!d) (flat D.low) j).Minimal
  let B := free.filter keep
  have sub : free ⊆ L.band r i := Finset.filter_subset ..
  have first : pins.mass (L.band r i) ≤ pins.mass free + err := by
    apply pins.retain (fun s => ¬r.Straddles d s area i) L.band_sub
    simpa only [not_not] using he
  have hb := L.bound hr hi (show flat (2*D.near) ≤ flat D.limit from fun _ => base)
  have second := pins.retain keep (sub.trans L.band_sub) (L.discard hb hr hj le_rfl)
  refine ⟨B,(Finset.filter_subset ..).trans sub,by unfold B; linarith,?_⟩
  intro g hg ht s hs
  obtain ⟨hs,hm⟩ := Finset.mem_filter.mp hs
  obtain ⟨hs,hn⟩ := Finset.mem_filter.mp hs
  exact L.persists hs hn hm ht (hh _ hg ht)

theorem barriers (hr : r.Finer old) (hi : w.place i ∈ area) {err b : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err)
    (hb : b ≤ pins.mass (L.band r i)) (hpos : 0 < b) (herr : err + L.loss ≤ b/4)
    (hbeta : 12*L.beta < b^2) :
    ∃ t ∈ L.band r i, ∃ B, b/4 ≤ pins.mass B ∧
      (∀ g, w.place g ∈ area → w.Ray area d i g → B ⊆ L.band r g) ∧
      ∀ s ∈ B, s.Nonempty ∧ ∀ g ∈ s, ∀ j ∈ t, w.rank j < w.rank g := by
  obtain ⟨C,hC,hm,hall⟩ := L.common hr hi he
  have big : 3*L.beta < (pins.mass C)^2 := by nlinarith
  let c := L.core r hi (base (D := D))
  have sub := hC.trans L.band_sub
  have hs : ∀ s ∈ C, c.Cut s := fun _ h => L.cut hi base (sub h)
  obtain ⟨t,ht,hh⟩ := (c.heavy pins C hs (L.bad hr hi base sub sub) big).2
  refine ⟨t,hC ht,_,le_trans (by linarith) hh.le,fun g hg ht => (Finset.filter_subset ..).trans (hall g hg ht),?_⟩
  intro s h
  obtain ⟨h,hn⟩ := Finset.mem_filter.mp h
  exact ⟨(c.refines _ (hs _ h).1).nonempty c.inhabited,fun g hg => (hn.2.2 g hg).2⟩

end Ledger
end OAI.Geometry.Hirsch.Layer.Board
end

-- SpineBounds
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}

omit [Fintype I] in
theorem Pins.extra_hit (pins : Pins p I) (s t : Finset I) (hd : Disjoint t s) :
    p.prob (fun x => s ⊆ pins.success x ∧ ∃ g ∈ t, g ∈ pins.success x) ≤ t.card * pins.rate * pins.weight s :=
  pins.extra s t (fun _ h => Finset.disjoint_left.mp hd h)



namespace Board.Ledger

variable {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A) {i j : I} {s : Finset I} {fresh : Pins p I} (draw : gate.Draw fresh)

def sharp (_L : Ledger gate old area d D M A) (b : Budget) := b + flat ((K+2)*D.step)

def error (U : ℝ) (z : ℝ) := Trial.Tests.capacity K D.max D.step * U * z^K + (K+1)*L.loss

theorem extract (hr : r.Finer old) (hi : w.place i ∈ area) {b : Budget} (hb : b ≤ flat (D.band+1))
    {U : ℝ} (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (L.sharp b) i).Covers (draw.thin x) ∧
      ¬∃ s ∈ L.book r i b, s ⊆ draw.thin x) ≤ L.error U fresh.rate := by
  let a := fun j => b + flat (j*D.step)
  have zero : a 0 = b := by ext; simp [a,flat]
  have next : ∀ j, a j + flat D.step ≤ a (j+1) := by
    intro j x; simp [a,flat,add_mul,add_assoc]
  have bound : ∀ j ≤ K+2, a j ≤ flat D.max := by
    intro j hj x
    exact Nat.add_le_add (hb x) (Nat.mul_le_mul_right _ hj)
  let paths := fun j => r.test area (!d) (a j) i
  have hs := serves hr i _ _ (bound (K+1) (by omega)) (next (K+1)) L.available
  have he := draw.extract hs (r.test area (!d) (flat D.near) i) paths
    (fun j _ => Round.test_mono _ _ _ _ (by rw [zero]; exact le_self_add))
    (fun _ h => h)
    (fun j hj => L.discard (L.bounds _ hr _ hi _ _ (bound _ (by omega)) (next j)) hr hi (Nat.le_succ _))
    ((p.mono fun _ h => hr.test (le_add_self.trans (next (K+1))) _ h).trans hu)
  change p.prob (fun x => (r.test area (!d) (L.sharp b) i).Covers (draw.thin x) ∧
      ¬∃ s ∈ L.book r i (a 0), s ⊆ draw.thin x) ≤ L.error U fresh.rate at he
  rwa [zero] at he

theorem neutral (hr : r.Finer old) (hi : w.place i ∈ area)
    {U : ℝ} (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (flat D.max) i).Covers (draw.thin x)) ≤
      L.error U fresh.rate + pins.mass (L.band r i) := by
  have hb := (L.range_depth i).2
  have h := L.extract draw hr hi hb hu
  apply le_trans _ ((p.either _ _).trans (add_le_add h (pins.family (L.band r i))))
  apply p.mono
  intro x hc
  by_cases hh : ∃ s ∈ L.band r i, s ⊆ draw.thin x
  · obtain ⟨s,hs,hh⟩ := hh
    exact .inr ⟨s,hs,hh.trans (draw.pinned x)⟩
  · exact .inl ⟨Round.test_mono _ _ _ _ (fun j => Nat.add_le_add_right (hb j) _) _ hc,hh⟩

theorem same_site (hr : r.Finer old) (hs : s ∈ L.book r i (flat D.limit))
    (hn : ¬r.Straddles d s area i) (ho : r.On area d i j) {x : Ω}
    (hx : s ⊆ draw.thin x) (hj : j ∈ draw.thin x) : w.place j ∈ s.image w.place := by
  obtain ⟨path,b,ht,hb,hmiss⟩ := Round.missed_ray ho.info.2.2.1 hn
  have small : b ≤ flat 1 := le_self_add.trans (hb.le.trans (w.ahead_one d i))
  have cost : b + flat D.step ≤ flat D.limit := by
    intro k
    have := small k
    have := D.order
    simp only [Depths.near,flat,Pi.add_apply] at *; omega
  have hc := hr.test le_rfl _ (ht.carry hmiss (L.mem.mp hs).2.1 cost)
  obtain ⟨y,hy⟩ := draw.old x
  have pass : draw.thin x ⊆ gate.pass y := Finset.inter_subset_left.trans hy
  obtain ⟨l,hl,hh⟩ := L.available y j ho.info.2.1 (gate.screen _ _ (pass hj))
  obtain ⟨g,hg,hm⟩ := hc l hl
  exact Finset.mem_image.mpr ⟨g,hm,hh g hg (pass (hx hm))⟩

theorem joint_hit (hr : r.Finer old) (hi : w.place i ∈ area) {err U : ℝ}
    (he : pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err)
    (hu : p.prob (fun x => (old.test area (!d) (flat D.step) i).Covers (draw.available x)) ≤ U) :
    p.prob (fun x => (r.test area (!d) (L.depth i) i).Covers (draw.thin x) ∧
      r.Straddles d (draw.thin x) area i) ≤ L.error U fresh.rate + err + K*pins.rate*M := by
  let B := L.book r i (flat D.limit)
  let C := B.filter fun s => r.Straddles d s area i
  let E := fun s x => s ⊆ draw.thin x ∧ r.Straddles d (draw.thin x) area i ∧ ¬r.Straddles d s area i
  have each : ∀ s ∈ B, p.prob (E s) ≤ K*pins.rate*pins.weight s := by
    intro s hs
    let t := Finset.univ.filter fun j => r.On area d i j ∧ w.place j ∈ s.image w.place ∧ j ∉ s
    have dis : Disjoint t s := Finset.disjoint_left.mpr fun _ h => (Finset.mem_filter.mp h).2.2.2
    have card : t.card ≤ K := by
      have eq : (t.image w.place).card = t.card := Finset.card_image_iff.mpr (by
        intro u hu v hv he
        exact (Finset.mem_filter.mp hu).2.1.unique (Finset.mem_filter.mp hv).2.1 he)
      have sub : t.image w.place ⊆ s.image w.place := by
        rintro _ hz
        obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hz
        exact (Finset.mem_filter.mp hg).2.2.1
      rw [← eq]; exact (Finset.card_le_card sub).trans (Finset.card_image_le.trans (L.mem.mp hs).1)
    apply le_trans _ ((pins.extra_hit s t dis).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr card) pins.pos.le) (pins.positive s).le))
    apply p.mono
    rintro x ⟨hx,⟨j,hj,ho⟩,hn⟩
    exact ⟨hx.trans (draw.pinned x),j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho,
      L.same_site draw hr hs hn ho hx hj,fun h => hn ⟨j,h,ho⟩⟩,draw.pinned x hj⟩
  have hsum : p.prob (fun x => ∃ s ∈ B, E s x) ≤ K*pins.rate*M := by
    apply ((p.union_finset B E).trans (Finset.sum_le_sum each)).trans
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (L.bound hr hi (fun _ => base)).mass (mul_nonneg (by positivity) pins.pos.le)
  have hex := L.extract draw hr hi (b := flat D.limit) (fun _ => D.order.2.2.2.1.trans (Nat.le_succ _)) hu
  have hh := (p.either _ _).trans (add_le_add hex ((pins.family C).trans he))
  apply le_trans _ ((p.either _ _).trans (add_le_add hh hsum))
  apply p.mono
  rintro x ⟨hc,ho⟩
  by_cases hs : ∃ s ∈ B, s ⊆ draw.thin x
  swap
  · exact .inl (.inl ⟨Round.test_mono _ _ _ _ (L.range_depth i).1 _ hc,hs⟩)
  obtain ⟨s,hs,hx⟩ := hs
  by_cases hn : r.Straddles d s area i
  · exact .inl (.inr ⟨s,Finset.mem_filter.mpr ⟨hs,hn⟩,hx.trans (draw.pinned x)⟩)
  · exact .inr ⟨s,hs,hx,ho,hn⟩

end Board.Ledger
end OAI.Geometry.Hirsch.Layer
end

-- Direction
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I} {n K : ℕ} {w : Board I n}
  {q r : w.Round} {area : Set ℕ} {d : Bool} {P : I → Prop} {i : I} {a : Ω → Finset I}

namespace Round

def Cover (q : w.Round) (area : Set ℕ) (d : Bool) (R : ℕ) (a : Ω → Finset I) (i : I) (x : Ω) :=
  (q.test area d (flat R) i).Covers (a x)

theorem Links.start (link : q.Links d P) (dir : Bool) (hi : w.place i ∈ area) :
    [] ∈ q.test area dir (flat 1) i ∨ ∃ y l, P y ∧ w.Shore d y ∧ w.place y ∈ area ∧
      q.Trip area i y (flat 2) l ∧ l.toFinset.card ≤ 2 := by
  obtain ⟨l,hl,hh⟩ := q.spine hi dir
  cases l with
  | nil => exact .inl hl
  | cons g rest =>
    right
    have ho := hh g (by simp)
    obtain ⟨j,_,ht⟩ := hl
    change q.Trip area i j (flat 1) ([] ++ g :: rest) at ht
    by_cases he : dir = d
    · subst dir
      obtain ⟨u,_,_,hm,he⟩ := ho
      have hg : P g := he ▸ link.east _ hm
      have ho := hh g (by simp)
      exact ⟨g,[g],hg,ho.info.1,ho.info.2.1,ht.redirect.more (fun _ => by norm_num [flat]),by simp⟩
    · have he' : dir = !d := by cases dir <;> cases d <;> simp_all
      obtain ⟨y,l,hy,hs,hp,ht,hl⟩ := link.divert ht (he' ▸ ho.info.1)
      refine ⟨y,l,hy,hs,hp.symm ▸ ho.info.2.1,ht,?_⟩
      have sub : l.toFinset ⊆ {g,y} := by
        intro k hk; simpa using hl (List.mem_toFinset.mp hk)
      exact (Finset.card_le_card sub).trans ((Finset.card_insert_le ..).trans (by simp))

theorem Links.reduce (link : q.Links d P) (dir : Bool) (hi : w.place i ∈ area)
    (pin : ∀ x, a x ⊆ pins.success x) {R : ℕ} {B : ℝ} (hn : 0 ≤ B)
    (bound : ∀ y, P y → w.Shore d y → w.place y ∈ area → p.prob (q.Cover area dir R a y) ≤ B) :
    p.prob (q.Cover area dir (2+R) a i) ≤ 2*pins.rate + B := by
  rcases link.start dir hi with he | ⟨y,l,hy,hs,hp,ht,hk⟩
  · have hh : ∀ x, ¬q.Cover area dir (2+R) a i x := by
      intro x hc
      have h := test_mono _ _ _ _ (show flat 1 ≤ flat (2+R) from fun _ => by simp only [flat]; omega) _ hc _ he
      simp [Trial.Hit] at h
    simp only [Law.prob,hh,↓reduceIte,Finset.sum_const_zero]; linarith [pins.pos]
  have hhit : p.prob (fun x => Trial.Hit (a x) l) ≤ 2*pins.rate := by
    have hb := pins.extra_hit ∅ l.toFinset (Finset.disjoint_empty_right _)
    simp only [Finset.empty_subset,true_and,Pins.weight,Finset.card_empty,pow_zero,mul_one] at hb
    exact ((p.mono fun x ⟨g,hg,hm⟩ => ⟨g,List.mem_toFinset.mpr hg,pin x hm⟩).trans hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) pins.pos.le)
  apply le_trans _ ((p.either _ _).trans (add_le_add hhit (bound y hy hs hp)))
  apply p.mono
  intro x hc
  by_cases h : Trial.Hit (a x) l
  · exact .inl h
  · exact .inr (ht.carry h hc le_rfl)

theorem Finer.escape (hr : q.Finer r) {R F : ℕ} {b : Budget} (hb : b ≤ flat F)
    {s t u : Finset I} (hsub : u ⊆ s) (hc : (q.test area d (flat (F+R)) i).Covers u)
    (hmiss : ¬(r.test area (!d) b i).Covers s) (ht : (r.test area (!d) b i).Covers t) :
    ∃ g ∈ t, (q.test area d (flat R) g).Covers u := by
  obtain ⟨l,hl,hn⟩ := Trial.missed hmiss
  obtain ⟨pre,g,rest,rfl,_,hg⟩ := (ht _ hl).first
  obtain ⟨_,_,hpath⟩ := hl
  obtain ⟨l,hl,h⟩ := hr.trip (hpath.redirect.more hb)
  refine ⟨g,hg,hl.carry ?_ hc le_rfl⟩
  rintro ⟨j,hj,hm⟩
  have hh := h hj
  exact hn ⟨j,by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; tauto,hsub hm⟩

end Round

namespace Ledger

variable [Fintype I] {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old : w.Round} {D : Depths K} {M A : ℝ} (L : Ledger gate old area d D M A)
  {fresh : Pins p I} (draw : gate.Draw fresh)

structure Switched (r q : w.Round) (P : I → Prop) (a : Ω → Finset I) (b err v U : ℝ) : Prop where
  mid : r.Finer old
  last : q.Finer r
  link : q.Links d P
  thinned : ∀ x, a x ⊆ draw.thin x
  crude : ∀ i, w.place i ∈ area → p.prob (old.Cover area (!d) D.step draw.available i) ≤ U
  rare : ∀ i, w.place i ∈ area → w.Shore d i →
    pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ err
  large : ∀ i, w.place i ∈ area → P i → b ≤ pins.mass (L.band r i)
  positive : 0 < b
  small : err+L.loss ≤ b/4
  pairs : 12*L.beta < b^2
  nonneg : 0 ≤ v
  shared : ∀ B, b/4 ≤ pins.mass B → ∃ event : Ω → Prop, p.prob event ≤ v ∧
    (∀ g, w.place g ∈ area → P g → B ⊆ L.band r g → ∀ x, g ∈ a x → event x) ∧
    ∀ j, (∀ s ∈ B, s.Nonempty ∧ ∀ g ∈ s, w.rank j < w.rank g) →
      ∀ R, p.Independent event (q.Cover area d R a j)

namespace Switched

variable {L draw} {b err v U : ℝ} (h : L.Switched draw r q P a b err v U)

include h in
theorem at_key (hi : w.place i ∈ area) (he : w.Shore d i) (hp : P i)
    {R : ℕ} {S : ℝ} (hS : 0 ≤ S) (bound : ∀ j, w.place j ∈ area → p.prob (q.Cover area d R a j) ≤ S) :
    p.prob (q.Cover area d (D.max+R) a i) ≤ L.error U fresh.rate + err + K*pins.rate*M + K*v*S := by
  have rare := h.rare i hi he
  obtain ⟨t,ht,B,hB,hall,hrank⟩ := L.barriers h.mid hi rare (h.large i hi hp) h.positive h.small h.pairs
  obtain ⟨e,he,pass,indep⟩ := h.shared B hB
  have hc := L.cut hi base (L.band_sub ht)
  have inside : ∀ j ∈ t, w.place j ∈ area := fun _ hj =>
    Round.keys_inside ((L.core r hi base).refines _ hc.1) hc.2 hj
  have each : ∀ j ∈ t, p.prob (fun x => e x ∧ q.Cover area d R a j x) ≤ v*S := by
    intro j hj
    rw [indep j (fun s hs => ⟨(hrank _ hs).1,fun g hg => (hrank _ hs).2 g hg j hj⟩) R]
    exact mul_le_mul he (bound _ (inside _ hj)) (p.positive _) h.nonneg
  have high : p.prob (fun x => ∃ j ∈ t, e x ∧ q.Cover area d R a j x) ≤ K*v*S := by
    apply ((p.union_finset t _).trans (Finset.sum_le_sum each)).trans
    rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (L.mem.mp ht).1) (mul_nonneg h.nonneg hS)
  have low := L.joint_hit draw h.mid hi rare (h.crude _ hi)
  apply le_trans _ ((p.either _ _).trans (add_le_add low high))
  apply p.mono
  intro x hx
  have hD := D.order
  obtain ⟨g,hg,ho⟩ := Round.hits hi (show flat 1 ≤ flat (D.max+R) from fun _ => by simp only [flat]; omega) hx
  by_cases hwest : (r.test area (!d) (L.depth i) i).Covers (draw.thin x)
  · exact .inl ⟨hwest,g,h.thinned x hg,h.last.on ho⟩
  have hd : L.depth i ≤ flat D.max := (L.range_depth _).2.trans (fun _ => hD.2.2.2.2)
  obtain ⟨j,hj,hcov⟩ := h.last.escape hd (h.thinned x) hx hwest (L.mem.mp ht).2.1
  have pg : P g := by obtain ⟨u,_,_,hm,rfl⟩ := ho; exact h.link.east u hm
  exact .inr ⟨j,hj,pass g ho.info.2.1 pg (hall g ho.info.2.1 ho.info.2.2.1) x hg,hcov⟩

include h in
theorem iterate {t : ℝ} (ht : 0 ≤ t) (herr : 0 ≤ err) (hU : 0 ≤ U)
    (he : 2*pins.rate + L.error U fresh.rate + err + K*pins.rate*M ≤ t/4)
    (hv : K*v ≤ 1/2) (j : ℕ) (hi : w.place i ∈ area) :
    p.prob (q.Cover area d (j*(2+D.max)) a i) ≤ t/2 + (K*v)^j := by
  have vpos := h.nonneg
  induction j generalizing i with
  | zero =>
    rw [pow_zero]
    linarith [p.positive (fun x => ¬q.Cover area d (0*(2+D.max)) a i x),
      p.neg (q.Cover area d (0*(2+D.max)) a i)]
  | succ j ih =>
    let S := t/2+(K*v)^j
    have hS : 0 ≤ S := by unfold S; positivity
    have hpos : 0 ≤ L.error U fresh.rate + err + K*pins.rate*M + K*v*S := by
      have := fresh.pos
      have := pins.pos
      have := L.positive.1
      have := L.mass
      unfold error; positivity
    have hb := h.link.reduce d hi (fun x => (h.thinned x).trans (draw.pinned x)) hpos
      (fun _ hp he hi => h.at_key hi he hp hS (fun _ hi => ih hi))
    rw [Nat.succ_mul,add_comm (j*_ ),add_assoc,pow_succ']
    apply hb.trans
    unfold S
    linarith only [he,mul_le_mul_of_nonneg_right hv ht]

end Switched
end Ledger
end OAI.Geometry.Hirsch.Layer.Board
end

-- Cluster
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Coins

variable {Bit I : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] (coin : Coins Bit)

theorem selected {S : Set Bit} {pick : Table Bit → Option I} (hp : Table.Reads S pick)
    (ev : I → Table Bit → Prop) {U : ℝ} (hu : 0 ≤ U)
    (hh : ∀ i, Table.Reads Sᶜ (ev i) ∧ coin.law.prob (ev i) ≤ U) :
    coin.law.prob (fun x => ∃ i, pick x = some i ∧ ev i x) ≤ U := by
  let chosen := fun i x => pick x = some i
  have mass : ∑ i, coin.law.prob (chosen i) ≤ 1 := by
    have hm := coin.law.multiplicity Finset.univ chosen (fun _ => True) (M := 1) (by
      intro x
      apply Finset.card_le_one.mpr
      intro i hi j hj
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
      exact Option.some.inj (hi.symm.trans hj)) (by simp)
    simpa [coin.law.certain (fun _ => True.intro)] using hm
  calc
    _ ≤ ∑ i, coin.law.prob (fun x => chosen i x ∧ ev i x) := coin.law.union _
    _ ≤ ∑ i, coin.law.prob (chosen i)*U := by
      apply Finset.sum_le_sum
      intro i _
      have h : Table.Reads Sᶜᶜ (chosen i) := by
        rw [compl_compl]
        exact fun x y hx => congrArg (· = some i) (hp x y hx)
      rw [coin.independent h (hh i).1]
      exact mul_le_mul_of_nonneg_left (hh i).2 (coin.law.positive _)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hu mass

end Coins

namespace Board.Round

variable {I : Type} {n : ℕ} {w : Board I n} {r : w.Round} {d : Bool} {area A B : Set ℕ}
  {i j : I} {b : Budget} {l : List I}

def portion (area : Set ℕ) (b : Budget) : Budget := fun x => if x/3 ∈ area then b x else 0

theorem Trip.portion (ht : r.Trip area i j b l) : r.Trip area i j (portion area b) l := by
  induction ht with
  | nil => exact .nil
  | @go i j k d b a path hi hm ha ht ih =>
    refine .go hi hm ?_ ih
    intro x
    by_cases hx : x/3 ∈ area
    · simpa [Round.portion,hx] using ha x
    · have hh : x ≠ w.layer i := fun e => hx (e.symm ▸ hi)
      simp [Round.portion,hx,atLayer,hh]

theorem Trip.join {k : I} {path : List I} (ht : r.Trip A i j b l) (hu : r.Trip B j k b path)
    (hd : Disjoint A B) : r.Trip (A ∪ B) i k b (l ++ path) := by
  apply ((ht.portion.widen Set.subset_union_left).append (hu.portion.widen Set.subset_union_right)).more
  intro x
  by_cases hx : x/3 ∈ A
  · have := Set.disjoint_left.mp hd hx; simp [Round.portion,hx,this]
  · simp only [Pi.add_apply,Round.portion,if_neg hx,zero_add]; split <;> omega

theorem Trip.exits (ht : r.Trip area i j b l) (hi : w.place i ∈ area)
    (hj : w.place j ∉ area) (hs : w.Shore (!d) j) :
    ∃ x ∈ area, if d then x+1 = w.place j else w.place j+1 = x := by
  induction ht with
  | nil => contradiction
  | @go i j k e b a path h hm ha ht ih =>
    by_cases hh : w.place j ∈ area
    · exact ih hh hj hs
    have he : j = k := by cases ht <;> simp_all
    subst k
    rcases hm with ⟨hl,rfl | jump⟩
    · have h₁ := w.east i hl
      have h₂ := w.west i hl
      have ne : w.place (w.step i e) ≠ w.place i := fun he => hj (he.symm ▸ hi)
      refine ⟨w.place i,hi,?_⟩
      cases d <;> cases e <;> simp [place,Shore] at hs ne ⊢ <;> omega
    · exact (hh ((show w.place j = w.place i from congrArg (· / 3) (r.localJump _ _ _ jump).2.1).symm ▸ hi)).elim

def Precedes (d : Bool) (A B : Set ℕ) := ∀ x ∈ A, ∀ y ∈ B, if d then x < y else y < x

theorem Precedes.disjoint (h : Precedes d A B) : Disjoint A B :=
  Set.disjoint_left.mpr fun x hx hy => by have := h x hx x hy; split at this <;> omega

theorem Precedes.ends (h : Precedes d A B) (hi : w.place i ∈ B)
    (ht : r.Trip B i j b l) (he : Ends w B d j) : Ends w (A ∪ B) d j := by
  rcases he with ⟨hj,hn⟩ | ⟨hj,hs⟩
  · exact .inl ⟨.inr hj,hn⟩
  obtain ⟨x,hx,he⟩ := ht.exits hi hj hs
  have hn : w.place j ∉ A := by
    intro hh
    have := h _ hh x hx
    cases d <;> simp_all <;> omega
  exact .inr ⟨fun hh => hh.elim hn hj,hs⟩

def restrict (w : Board I n) (area : Set ℕ) (s : Finset I) := s.filter fun g => w.place g ∈ area

theorem Trip.hit (ht : r.Trip area i j b l) (s : Finset I) :
    Trial.Hit (restrict w area s) l ↔ Trial.Hit s l :=
  ⟨fun h => h.mono (Finset.filter_subset ..),fun ⟨g,hg,hm⟩ => ⟨g,hg,Finset.mem_filter.mpr ⟨hm,(ht.member hg).1⟩⟩⟩

variable {Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {a : Table Bit → Finset I} {R : ℕ}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem reads_cover {S : Set Bit}
    (read : ∀ g, w.place g ∈ area → w.rank g < w.rank i → Table.Reads S (fun x => g ∈ a x)) :
    Table.Reads S (r.Cover area d R a i) := by
  intro x y h
  have eq : ∀ l ∈ r.test area d (flat R) i, Trial.Hit (a x) l ↔ Trial.Hit (a y) l := by
    rintro l ⟨j,_,ht⟩
    have same := fun g hg => read g (ht.member hg).1 (ht.member hg).2 x y h
    exact ⟨fun ⟨g,hg,hm⟩ => ⟨g,hg,(same g hg).mp hm⟩,fun ⟨g,hg,hm⟩ => ⟨g,hg,(same g hg).mpr hm⟩⟩
  exact propext ⟨fun hc l hl => (eq l hl).mp (hc l hl),fun hc l hl => (eq l hl).mpr (hc l hl)⟩

structure Cap (coin : Coins Bit) (r : w.Round) (d : Bool) (R : ℕ) (a : Table Bit → Finset I)
    (area : Set ℕ) (S : Set Bit) (U : ℝ) : Prop where
  nonneg : 0 ≤ U
  reads : ∀ i, w.place i ∈ area → Table.Reads S (fun x => i ∈ a x)
  bound : ∀ i, w.place i ∈ area → coin.law.prob (r.Cover area d R a i) ≤ U

theorem Cap.join {S T : Set Bit} {U V : ℝ} (ha : Cap coin r d R a A S U) (hb : Cap coin r d R a B T V)
    (h : Precedes d A B) (hd : Disjoint S T) : Cap coin r d R a (A ∪ B) (S ∪ T) (U+V) := by
  refine ⟨add_nonneg ha.nonneg hb.nonneg,fun i hi => hi.elim (fun h => (ha.reads i h).mono Set.subset_union_left)
    (fun h => (hb.reads i h).mono Set.subset_union_right),?_⟩
  intro i hi
  rcases hi with hi | hi
  swap
  · apply le_trans _ ((hb.bound i hi).trans (le_add_of_nonneg_left ha.nonneg))
    apply coin.law.mono
    rintro x hc l ⟨j,he,ht⟩
    exact hc _ ⟨j,h.ends hi ht he,ht.widen Set.subset_union_right⟩
  let missed := fun s j => ∃ l, Ends w A d j ∧ r.Trip A i j (flat R) l ∧ ¬Trial.Hit s l
  let pick := fun s => if hh : ∃ j, missed s j then some hh.choose else none
  let sel := fun x => pick (restrict w A (a x))
  have reads : Table.Reads S sel := by
    intro x y he
    apply congrArg pick
    ext g
    by_cases hg : w.place g ∈ A
    · simpa [restrict,hg] using iff_of_eq (ha.reads g hg x y he)
    · simp [restrict,hg]
  let ev := fun j x => w.place j ∈ B ∧ r.Cover B d R a j x
  have hh := coin.selected reads ev hb.nonneg (by
    intro j
    constructor
    · have hr : Table.Reads T (r.Cover B d R a j) := reads_cover (fun g hg _ => hb.reads g hg)
      exact fun x y he => congrArg (And (w.place j ∈ B)) (hr x y (he.mono (fun _ ht hs => Set.disjoint_left.mp hd hs ht)))
    · by_cases hj : w.place j ∈ B
      · exact (coin.law.mono fun _ hh => hh.2).trans (hb.bound j hj)
      · simpa [ev,hj,Law.prob] using hb.nonneg)
  apply le_trans _ ((coin.law.either _ _).trans (add_le_add (ha.bound i hi) hh))
  apply coin.law.mono
  intro x hc
  by_cases hc' : r.Cover A d R a i x
  · exact .inl hc'
  right
  have ex : ∃ j, missed (restrict w A (a x)) j := by
    obtain ⟨l,⟨j,he,ht⟩,hm⟩ := Trial.missed hc'
    exact ⟨j,l,he,ht,fun h => hm ((ht.hit _).mp h)⟩
  obtain ⟨l,he,ht,hm⟩ := ex.choose_spec
  have hn : ¬Trial.Hit (a x) l := fun hh => hm ((ht.hit _).mpr hh)
  have hj : w.place ex.choose ∈ B := by
    by_contra h'
    apply hn (hc _ ⟨_,?_,ht.widen Set.subset_union_left⟩)
    exact he.imp (fun h => ⟨.inl h.1,h.2⟩) (fun h => ⟨fun hh => hh.elim h.1 h',h.2⟩)
  refine ⟨ex.choose,by simp [sel,pick,ex],hj,?_⟩
  rintro l' ⟨k,hk,hu⟩
  obtain ⟨g,hg,hga⟩ := hc _ ⟨k,h.ends hj hu hk,ht.join hu h.disjoint⟩
  exact ⟨g,(List.mem_append.mp hg).resolve_left (fun h => hn ⟨g,h,hga⟩),hga⟩

end Board.Round
end OAI.Geometry.Hirsch.Layer
end

-- Merge
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

def piece (width j : ℕ) : Set ℕ := {x | x/width = j}

def pieces (width j a : ℕ) : Set ℕ := {x | j ≤ x/width ∧ x/width < j+a}

theorem pieces_succ (width j a : ℕ) :
    pieces width j (a+1) = pieces width j a ∪ piece width (j+a) := by
  ext x; simp only [pieces,piece,Set.mem_ofPred_eq,Set.mem_union]; omega

theorem pieces_eq (width j a : ℕ) (ha : 0 < a) :
    pieces width (j*a) a = piece (width*a) j := by
  ext x
  simp only [pieces,piece,Set.mem_ofPred_eq,← Nat.div_div_eq_div_mul]
  rw [show j*a+a = (j+1)*a by ring,← Nat.le_div_iff_mul_le ha,← Nat.div_lt_iff_lt_mul ha]
  omega

variable {I Bit : Type} {n : ℕ} (w : Board I n) (keys : Bit → Finset I)

def home (width : ℕ) (i : I) := piece width (w.place i / width)

theorem home_eq {width j : ℕ} {i : I} (h : w.place i ∈ piece width j) : w.home width i = piece width j :=
  congrArg (piece width) h

theorem home_sub (width a : ℕ) (i : I) : w.home width i ⊆ w.home (width*a) i := by
  intro x hx
  change x/width = w.place i/width at hx
  change x/(width*a) = w.place i/(width*a)
  simp only [← Nat.div_div_eq_div_mul,hx]

def zone (area : Set ℕ) : Set Bit :=
  {b | (keys b).Nonempty ∧ ∀ g ∈ keys b, w.place g ∈ area}

theorem zone_mono {area region : Set ℕ} (h : area ⊆ region) : w.zone keys area ⊆ w.zone keys region :=
  fun _ hb => ⟨hb.1,fun _ hg => h (hb.2 _ hg)⟩

theorem zone_disjoint {A B : Set ℕ} (hd : Disjoint A B) : Disjoint (w.zone keys A) (w.zone keys B) := by
  apply Set.disjoint_left.mpr
  rintro b ⟨⟨g,hg⟩,hA⟩ ⟨_,hB⟩
  exact Set.disjoint_left.mp hd (hA _ hg) (hB _ hg)

namespace Round

variable {w keys} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {r : w.Round} {d : Bool} {R : ℕ} {select : Table Bit → Finset I} {U : ℝ}

def Caps (coin : Coins Bit) (keys : Bit → Finset I) (r : w.Round) (d : Bool) (R : ℕ)
    (select : Table Bit → Finset I) (width : ℕ) (U : ℝ) :=
  ∀ j, Cap coin r d R select (piece width j) (w.zone keys (piece width j)) U

theorem Caps.merge {width a : ℕ} (h : Caps coin keys r d R select width U) (ha : 0 < a) :
    Caps coin keys r d R select (width*a) (a*U) := by
  have aux : ∀ j k, Cap coin r d R select (pieces width j k) (w.zone keys (pieces width j k)) ((k : ℝ)*U) := by
    intro j k
    induction k with
    | zero =>
      have he : pieces width j 0 = ∅ := by ext; simp [pieces]
      rw [he,Nat.cast_zero,zero_mul]; exact ⟨le_rfl,by simp,by simp⟩
    | succ k ih =>
      rw [pieces_succ,Nat.cast_succ,add_mul,one_mul]
      let A := pieces width j k
      let B := piece width (j+k)
      have ord : Precedes true A B := by
        intro x hx y hy
        have lt : x/width < y/width := hx.2.trans_eq hy.symm
        exact lt_of_not_ge fun hh => lt.not_ge (Nat.div_le_div_right hh)
      have dis := w.zone_disjoint keys ord.disjoint
      have hh : Cap coin r d R select (A ∪ B) (w.zone keys A ∪ w.zone keys B) (k*U+U) := by
        cases d
        · rw [Set.union_comm A,Set.union_comm (w.zone keys A),add_comm]
          exact (h _).join ih (fun x hx y hy => ord y hy x hx) dis.symm
        · exact ih.join (h _) ord dis
      exact ⟨hh.nonneg,fun i hi => (hh.reads i hi).mono (Set.union_subset
        (w.zone_mono keys Set.subset_union_left) (w.zone_mono keys Set.subset_union_right)),hh.bound⟩
  intro j; rw [← pieces_eq width j a ha]; exact aux _ _

end Round
end OAI.Geometry.Hirsch.Layer.Board
end

-- Visibility
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} (rule : Coins.Rules raw)

namespace Coins

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_keep {s : Finset I} {x : Table Bit} {b : Bit} (hb : b ∉ raw.bitsOf s) :
    raw.force s x b = x b := by simp [force,Table.replace,hb]

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_empty (raw : coin.Raw I) (x : Table Bit) : raw.force ∅ x = x := by
  ext; simp [force,bitsOf,Table.replace]

omit [Fintype Bit] [Fintype I] in
theorem Raw.force_reads (raw : coin.Raw I) (s : Finset I) {S : Set Bit} {x y : Table Bit} (h : Set.EqOn x y S) :
    Set.EqOn (raw.force s x) (raw.force s y) S := by
  intro b hb
  simp only [force,Table.replace,h hb]

theorem Raw.force_pin (raw : coin.Raw I) {s : Finset I} {i : I} (hi : i ∉ s) (x : Table Bit) :
    i ∈ raw.pins.success (raw.force s x) ↔ i ∈ raw.pins.success x := by
  simp only [mem]
  apply iff_of_eq
  apply reads_all
  intro b hb
  apply force_keep
  rintro h
  obtain ⟨j,hj,hb'⟩ := Finset.mem_biUnion.mp h
  exact Finset.disjoint_left.mp (raw.unique i j (fun he => hi (he.symm ▸ hj))) hb hb'

def Rules.watch (hide s : Finset I) (x : Table Bit) := rule.pass (raw.force s x) \ hide

theorem Rules.watch_pin {hide s : Finset I} (hs : s ⊆ hide) (x : Table Bit) :
    rule.watch hide s x ⊆ raw.pins.success x := by
  intro g hg
  obtain ⟨hg,hn⟩ := Finset.mem_sdiff.mp hg
  exact (raw.force_pin (fun h => hn (hs h)) x).mp ((rule.mem ..).mp hg).1

end Coins

structure Stamp (Bit I : Type) where
  age : Bit → ℕ
  keys : Bit → Finset I
  pin : Bit → Prop

namespace Stamp

variable (tag : Stamp Bit I) {n : ℕ} (w : Board I n) {k width : ℕ}

def scope (k width : ℕ) (i : I) : Set Bit :=
  {b | tag.age b ≤ k ∧ b ∈ w.zone tag.keys (w.home width i) ∧ ∀ j ∈ tag.keys b, w.rank j ≤ w.rank i}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem scope_mono {i j : I} {k' width' : ℕ} (hk : k ≤ k') (hh : w.home width i ⊆ w.home width' j)
    (hr : w.rank i ≤ w.rank j) : tag.scope w k width i ⊆ tag.scope w k' width' j :=
  fun _ h => ⟨h.1.trans hk,w.zone_mono _ hh h.2.1,fun g hg => (h.2.2 g hg).trans hr⟩

def Tagged (raw : coin.Raw I) (k : ℕ) :=
  ∀ i b, b ∈ raw.bits i → tag.pin b ∧ tag.age b ≤ k ∧ tag.keys b = {i}

structure Visible (rule : Coins.Rules raw) (k width : ℕ) : Prop where
  pins : tag.Tagged raw k
  bars : ∀ i b, b ∈ rule.barriers i → ¬tag.pin b ∧ b ∈ tag.scope w k width i
  ok : ∀ i, Table.Reads (tag.scope w k width i) (rule.ok i)

variable {tag w rule}

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem Tagged.scope (ht : tag.Tagged raw k) (i : I) : ↑(raw.bits i) ⊆ tag.scope w k width i := by
  intro b hb
  obtain ⟨_,hk,he⟩ := ht i b hb
  refine ⟨hk,?_,?_⟩
  · simp [Board.zone,he,Board.home,Board.piece]
  · simp [he]

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem Tagged.whole (ht : tag.Tagged raw k) (i : I) :
    ∀ j b, b ∈ raw.bits j → b ∈ tag.scope w k width i → ↑(raw.bits j) ⊆ tag.scope w k width i := by
  intro j b hb hs c hc
  obtain ⟨_,_,he⟩ := ht _ _ hb
  obtain ⟨_,hk,hc⟩ := ht _ _ hc
  exact ⟨hk,by simpa only [Board.zone,Set.mem_ofPred_eq,he,hc] using hs.2⟩

namespace Visible

variable (h : tag.Visible w rule k width)

include h in
theorem pass (i : I) : Table.Reads (tag.scope w k width i) (fun x => i ∈ rule.pass x) := by
  intro x y he
  have hp := (Coins.reads_all (raw.bits i)).mono (h.pins.scope i) x y he
  have hb := (Coins.reads_all (rule.barriers i)).mono (fun b hb => (h.bars i b hb).2) x y he
  simp only [Coins.Rules.mem,Coins.Raw.mem,hp,hb,h.ok i x y he]

include h in
theorem watch (hide s : Finset I) (i : I) : Table.Reads (tag.scope w k width i)
    (fun x => i ∈ rule.watch hide s x) := by
  intro x y he
  simp only [Coins.Rules.watch,Finset.mem_sdiff,h.pass i _ _ (raw.force_reads s he)]

include h in
omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem enlarge (a : ℕ) : tag.Visible w rule k (width*a) := by
  have sub := fun i => tag.scope_mono w (k := k) le_rfl (w.home_sub width a i) le_rfl
  exact ⟨h.pins,fun i b hb => ⟨(h.bars i b hb).1,sub i (h.bars i b hb).2⟩,
    fun i => (h.ok i).mono (sub i)⟩

include h in
theorem cover (hide s : Finset I) (r : w.Round) (d : Bool) (R : ℕ) (i : I) :
    Table.Reads (tag.scope w k width i) (r.Cover (w.home width i) d R (rule.watch hide s) i) := by
  apply Board.Round.reads_cover
  intro j hj hr
  exact (h.watch hide s j).mono (tag.scope_mono w le_rfl (w.home_eq hj).subset hr.le)

end Visible

def hidden (w : Board I n) (g : I) := Finset.univ.filter fun i => w.place i = w.place g

def bad (rule : Coins.Rules raw) (r : w.Round) (d : Bool) (width R : ℕ) (g : I) :=
  r.Cover (w.home width g) d R (rule.watch (hidden w g) ∅) g

def Capped (tag : Stamp Bit I) (rule : Coins.Rules raw) (r : w.Round) (d : Bool) (width R : ℕ) (t : ℝ) :=
  ∀ hide s, s ⊆ hide → Board.Round.Caps coin tag.keys r d R (rule.watch hide s) width t

variable {r : w.Round} {d : Bool} {R K : ℕ} {t : ℝ}

theorem Visible.capped (h : tag.Visible w rule k width) (ht : 0 ≤ t)
    (hh : ∀ hide s, s ⊆ hide → ∀ i, coin.law.prob (r.Cover (w.home width i) d R (rule.watch hide s) i) ≤ t) :
    tag.Capped rule r d width R t := by
  intro hide s hs j
  refine ⟨ht,fun i hi => (h.watch hide s i).mono ?_,fun i hi => ?_⟩
  · rw [← w.home_eq hi]; exact fun _ hb => hb.2.1
  · rw [← w.home_eq hi]; exact hh hide s hs i

theorem Capped.merge (h : tag.Capped rule r d width R t) {a : ℕ} (ha : 0 < a) :
    tag.Capped rule r d (width*a) R (a*t) := fun hide s hs => (h hide s hs).merge ha

theorem Capped.given (h : tag.Capped rule r d width R t) (g : I) (s : Finset I)
    (hs : ∀ i ∈ s, w.place i = w.place g) : raw.pins.given (bad rule r d width R g) s ≤ t := by
  rw [← raw.forced]
  have sub : s ⊆ hidden w g := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs i hi⟩
  have hh := (h _ s sub (w.place g / width)).bound g rfl
  simp only [bad,Board.Round.Cover,Coins.Rules.watch,Coins.Raw.force_empty]
  exact hh

theorem Visible.screen (h : tag.Visible w rule k width) (thr : Thresholds K) :
    tag.Visible w (rule.screen thr (bad rule r d width R)) k width := by
  refine ⟨h.pins,h.bars,fun i => ?_⟩
  have he := h.cover (hidden w i) ∅ r d R i
  exact fun x y hh => congrArg₂ And (h.ok i x y hh) (raw.reads_screen he (h.pins.whole i) thr x y hh)

theorem available (rule : Coins.Rules raw) (thr : Thresholds K) {x : Table Bit} {g : I}
    (hn : ¬bad rule r d width R g x) :
    ∃ l ∈ r.test (w.home width g) d (Board.flat R) g,
      ∀ j ∈ l, j ∈ (rule.screen thr (bad rule r d width R)).pass x → w.place j = w.place g := by
  obtain ⟨l,hl,hm⟩ := Trial.missed hn
  refine ⟨l,hl,fun j hj hh => ?_⟩
  by_contra he
  apply hm
  refine ⟨j,hj,?_⟩
  simpa [Coins.Rules.watch,Coins.Raw.force_empty,hidden,he] using rule.screen_pass thr _ x hh

end Stamp
end OAI.Geometry.Hirsch.Layer
end

-- Fresh
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Stamp

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {rule : Rules raw} {n : ℕ} {w : Board I n} {k width : ℕ}
  {tag : Stamp Bit I}

structure Fresh (tag : Stamp Bit I) (fresh : coin.Raw I) (k : ℕ) : Prop where
  tagged : tag.Tagged fresh (k+1)
  age : ∀ i b, b ∈ fresh.bits i → tag.age b = k+1

namespace Fresh

variable (h : tag.Fresh fresh k) (hr : tag.Visible w rule k width)

include h hr in
omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem separate : raw.Separate fresh := by
  intro i j
  apply Finset.disjoint_left.mpr
  intro b hb hb'
  have := (hr.pins _ _ hb).2.1
  have := h.age _ _ hb'
  omega

include h in
omit [Fintype Bit] in
theorem previous (i : I) : tag.scope w k width i ⊆ (↑(fresh.bitsOf Finset.univ))ᶜ := by
  intro b hb hh
  obtain ⟨j,_,hb'⟩ := Finset.mem_biUnion.mp hh
  have := hb.1
  have := h.age _ _ hb'
  omega

include h hr in
omit [Fintype Bit] [Fintype I] in
theorem combined : tag.Tagged (raw.join fresh (h.separate hr)) (k+1) := by
  intro i b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · obtain ⟨hp,ha,hk⟩ := hr.pins i b hb
    exact ⟨hp,ha.trans (Nat.le_succ _),hk⟩
  · exact h.tagged i b hb

variable {K : ℕ} {gamma alpha : ℝ} (gate : Trial.Gates raw.pins w.place K gamma alpha)
  (he : gate.pass = rule.pass) (hide s : Finset I) (hs : s ⊆ hide)

def draw : gate.Draw fresh.pins where
  available := rule.watch hide s
  old x := ⟨raw.force s x,by rw [he]; exact Finset.sdiff_subset⟩
  pin := rule.watch_pin hs
  independent E t := by
    apply coin.independent (s := ↑(fresh.bitsOf Finset.univ))
    · intro x y eq
      apply congrArg E
      ext i
      exact iff_of_eq ((hr.watch hide s i).mono (h.previous i) x y eq)
    · apply (fresh.reads t).mono
      intro b hb
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩

variable (bars : I → Finset Bit) (hb : ∀ i b, b ∈ bars i → ¬tag.pin b ∧ b ∈ tag.scope w (k+1) width i)

include h hr hb in
omit [Fintype Bit] [Fintype I] in
theorem disjoint (i j : I) : Disjoint (rule.barriers i ∪ bars i) ((raw.join fresh (h.separate hr)).bits j) := by
  apply Finset.disjoint_left.mpr
  intro b hm hp
  rcases Finset.mem_union.mp hm with hm | hm
  · exact (hr.bars i b hm).1 (h.combined hr j b hp).1
  · exact (hb i b hm).1 (h.combined hr j b hp).1

def advance := rule.next (h.separate hr) bars (h.disjoint hr bars hb)

omit [Fintype Bit] [Fintype I] in
theorem visible : tag.Visible w (h.advance hr bars hb) (k+1) width := by
  have sub : ∀ i, tag.scope w k width i ⊆ tag.scope w (k+1) width i :=
    fun _ => tag.scope_mono w (Nat.le_succ k) Set.Subset.rfl le_rfl
  refine ⟨h.combined hr,fun i b hm => ?_,fun i => (hr.ok i).mono (sub i)⟩
  rcases Finset.mem_union.mp hm with hm | hm
  · exact ⟨(hr.bars _ _ hm).1,sub i (hr.bars _ _ hm).2⟩
  · exact hb _ _ hm

theorem reliable {margin loss v : ℝ} (hv : 0 < v) (hv' : v ≤ 1) (hv'' : ∀ i, v ≤ coin.weight (bars i))
    (hrel : rule.Reliable w.place K margin loss) :
    (h.advance hr bars hb).Reliable w.place K (margin*v) loss :=
  rule.reliable_next _ _ _ hrel (fun i => (hr.ok i).mono (h.previous i)) hv hv' hv''

theorem watched (x : Table Bit) (g : I) (hg : g ∈ (h.advance hr bars hb).watch hide s x) :
    g ∈ (h.draw hr gate he hide s hs).thin x ∧ All (bars g) x := by
  let total := raw.join fresh (h.separate hr)
  let y := total.force s x
  obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hg
  obtain ⟨hp,_,hall⟩ := (rule.next_pass _ _ _ y g).mp hm
  have old : g ∈ rule.pass (raw.force s x) := by
    apply (iff_of_eq (hr.pass g y _ ?_)).mp hp
    intro b hscope
    have eq : b ∈ total.bitsOf s ↔ b ∈ raw.bitsOf s := by
      simp only [Raw.bitsOf,Finset.mem_biUnion,total,Raw.join,Finset.mem_union]
      have no : ∀ i, b ∉ fresh.bits i := fun i hi => h.previous g hscope
        (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩)
      simp [no]
    simp only [y,Raw.force,Table.replace,Finset.mem_coe,eq]
  have pinned := (h.advance hr bars hb).watch_pin hs x hg
  rw [Raw.join_success] at pinned
  refine ⟨Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨old,hn⟩,(Finset.mem_inter.mp pinned).2⟩,?_⟩
  intro b hm
  have free : b ∉ total.bitsOf s := by
    rintro hh
    obtain ⟨j,_,hp⟩ := Finset.mem_biUnion.mp hh
    exact (hb _ _ hm).1 (h.combined hr j b hp).1
  exact (Raw.force_keep free).symm.trans (hall _ hm)

end Fresh
end OAI.Geometry.Hirsch.Layer.Stamp
end

-- Foil
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k width : ℕ} {L b : ℝ}

structure Foil (coin : Coins Bit) (tag : Stamp Bit I) (k : ℕ) (rate L b : ℝ) where
  index : Finset I → Bit
  age : ∀ s, tag.age (index s) = k
  keys : ∀ s, tag.keys (index s) = s
  barrier : ∀ s, ¬tag.pin (index s)
  bias : ∀ s, coin.bias (index s) = Real.exp ((-4*L/b)*rate^s.card)
  positive : 0 < b
  nonneg : 0 ≤ L

namespace Foil

variable {pins : Pins coin.law I} (f : Foil coin tag k pins.rate L b)
  (B : Finset (Finset I))

def bits := B.image f.index

omit [Fintype I] in
theorem weight : coin.weight (f.bits B) = Real.exp ((-4*L/b)*pins.mass B) := by
  unfold Coins.weight bits
  rw [Finset.prod_image (fun s _ t _ he => (f.keys s).symm.trans ((congrArg tag.keys he).trans (f.keys t)))]
  unfold Pins.mass Pins.weight
  rw [Finset.mul_sum,Real.exp_sum]
  exact Finset.prod_congr rfl fun s _ => f.bias s

omit [Fintype I] in
theorem low (h : pins.mass B ≤ 2*b) : Real.exp (-8*L) ≤ coin.weight (f.bits B) := by
  rw [f.weight,Real.exp_le_exp,div_mul_eq_mul_div,le_div_iff₀ f.positive]
  nlinarith only [mul_le_mul_of_nonneg_left h f.nonneg]

omit [Fintype I] in
theorem high (h : b/4 ≤ pins.mass B) : coin.law.prob (Coins.All (f.bits B)) ≤ Real.exp (-L) := by
  rw [coin.all_prob,f.weight,Real.exp_le_exp,div_mul_eq_mul_div,div_le_iff₀ f.positive]
  nlinarith only [mul_le_mul_of_nonneg_left h f.nonneg]

omit [Fintype I] in
theorem visible (i : I)
    (hh : ∀ s ∈ B, s.Nonempty ∧ ∀ j ∈ s, w.place j ∈ w.home width i ∧ w.rank j < w.rank i) :
    ∀ c ∈ f.bits B, ¬tag.pin c ∧ c ∈ tag.scope w k width i := by
  intro c hc
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hn,hh⟩ := hh s hs
  simp only [Stamp.scope,Board.zone,Set.mem_ofPred_eq,f.age,f.keys,le_refl,true_and]
  exact ⟨f.barrier _,⟨hn,fun j hj => (hh j hj).1⟩,fun j hj => (hh j hj).2.le⟩

theorem independent {raw : coin.Raw I} {rule : Coins.Rules raw} (hr : tag.Visible w rule k width)
    (hide s : Finset I) (q : w.Round) (area : Set ℕ) (d : Bool) (R : ℕ) (j : I)
    (hh : ∀ t ∈ B, t.Nonempty ∧ ∀ g ∈ t, w.rank j < w.rank g) :
    coin.law.Independent (Coins.All (f.bits B)) (q.Cover area d R (rule.watch hide s) j) := by
  apply coin.independent (s := (↑(f.bits B))ᶜ)
  · rw [compl_compl]; exact Coins.reads_all _
  apply Board.Round.reads_cover
  intro g _ hg
  apply (hr.watch hide s g).mono
  intro c hc hc'
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc'
  obtain ⟨⟨u,hu⟩,hlt⟩ := hh t ht
  have := hc.2.2 u ((f.keys _).symm ▸ hu)
  exact (hlt _ hu).not_ge (this.trans hg.le)

end Foil

namespace Board.Ledger

variable {Ω : Type} [Fintype Ω] {p : Law Ω} {pins : Pins p I}
  {K : ℕ} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (ledger : Ledger gate old area d D M A) {i : I}

theorem support (hi : w.place i ∈ area) {s : Finset I} (hs : s ∈ ledger.book r i (flat D.limit)) :
    s.Nonempty ∧ ∀ j ∈ s, w.place j ∈ area ∧ w.rank j < w.rank i := by
  let c := ledger.core r hi base
  have hc := ledger.cut hi base hs
  have h := c.refines _ hc.1
  exact ⟨h.nonempty c.inhabited,fun _ hj => ⟨Round.keys_inside h hc.2 hj,c.falls.older h hc.2 _ hj⟩⟩

end Board.Ledger

def price (t : ℝ) (j : ℕ) := t/4 * 2^j

theorem price_low {t : ℝ} (ht : 0 < t) (j : ℕ) : t/4 ≤ price t j :=
  le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))

theorem buckets {t m : ℝ} {J : ℕ} (hl : t/4 ≤ m) (hh : m < price t J) :
    ∃ j : Fin J, price t j ≤ m ∧ m < 2*price t j := by
  induction J with
  | zero => simp [price] at hh; linarith
  | succ J ih =>
    by_cases he : m < price t J
    · obtain ⟨j,hj⟩ := ih he
      exact ⟨j.castSucc,hj⟩
    · refine ⟨Fin.last J,le_of_not_gt he,?_⟩
      simpa [price,pow_succ',mul_left_comm] using hh

def bucket (t : ℝ) (J : ℕ) (m : ℝ) : Option (Fin J) :=
  if h : ∃ j : Fin J, price t j ≤ m ∧ m < 2*price t j then some h.choose else none

theorem bucket_high {t m : ℝ} {J : ℕ} {j : Fin J} (h : bucket t J m = some j) :
    price t j ≤ m ∧ m < 2*price t j := by
  unfold bucket at h
  split at h
  · rename_i hh; exact Option.some.inj h ▸ hh.choose_spec
  · contradiction

theorem bucket_low {t m : ℝ} {J : ℕ} (hh : m < price t J) (h : bucket t J m = none) : m < t/4 := by
  by_contra! he
  simp [bucket,buckets he hh] at h

end OAI.Geometry.Hirsch.Layer
end

-- Tuning
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

def depths (K cycles : ℕ) (hc : 0 < cycles) : ℕ → Board.Depths K
  | 0 => ⟨1,le_rfl⟩
  | k+1 => ⟨cycles*(2+(depths K cycles hc k).max),Nat.mul_pos hc (by omega)⟩

structure Dials where
  K : ℕ
  a : ℕ
  h : ℕ
  J : ℕ
  cycles : ℕ
  run : 0 < cycles
  tests : Thresholds K
  p : ℝ
  z : ℝ
  t : ℝ
  L : ℝ
  M : ℝ
  A : ℝ
  theta : ℝ
  gamma : ℝ

namespace Dials

variable (u : Dials)

def D := depths u.K u.cycles u.run
def rate (k : ℕ) := u.p*u.z^k
def margin (k : ℕ) := Real.exp (-8*u.L)^k
def cost (k : ℕ) := (k : ℝ)*((1+4^u.K)*u.tests.value u.K)
def err := Board.Ledger.factor u.a u.h ^ u.K * u.theta
def U := u.a*u.t
def loss := (u.K+1)*u.A*u.M
def key := (1+u.A)*u.p
def beta := 2*u.M*(u.K*(u.key+u.loss))
def capacity (k : ℕ) := Trial.Tests.capacity u.K (u.D k).max (u.D k).step
def error (k : ℕ) := u.capacity k*u.U*u.z^u.K + (u.K+1)*u.loss

structure Valid : Prop where
  keys : 2 ≤ u.K
  base : 2 ≤ u.a
  initial : 0 < u.p
  initial_le : u.p ≤ u.t
  target : u.t ≤ 1
  thin : 0 < u.z
  thin_le : u.z ≤ 1
  lambda : 0 ≤ u.L
  mass : 0 ≤ u.M
  link : 0 ≤ u.A
  scale : 0 < u.theta
  passage : 0 < u.gamma
  crude : u.U ≤ u.tests.value 0
  reliable : ∀ k ≤ u.h, u.gamma ≤ u.margin k ^ u.K - 2*u.K*u.cost (k+1)
  bounds : ∀ k < u.h, u.capacity k*u.U ≤ u.gamma*u.M ∧
    u.capacity k*(u.tests.value u.K+(u.K*(u.D k).max+(u.D k).step+1)*u.p) ≤ u.gamma*u.A
  compare : 3*u.beta < u.theta^2
  discard : u.key+u.loss ≤ u.theta
  rare : u.err ≤ u.t/32
  bins : u.M < price u.t u.J
  small : ∀ k < u.h, 2*u.p + u.error k + u.err + u.K*u.p*u.M ≤ u.t/4
  contraction : u.K*Real.exp (-u.L) ≤ 1/2
  stop : (u.K*Real.exp (-u.L))^u.cycles ≤ u.t/2

namespace Valid

variable {u} (v : u.Valid)
include v

theorem tpos : 0 < u.t := v.initial.trans_le v.initial_le
theorem crude_pos : 0 < u.U := mul_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) v.base) v.tpos
theorem rate_pos (k : ℕ) : 0 < u.rate k := mul_pos v.initial (pow_pos v.thin _)
theorem rate_le (k : ℕ) : u.rate k ≤ u.p := mul_le_of_le_one_right v.initial.le (pow_le_one₀ v.thin.le v.thin_le)
theorem loss_pos : 0 ≤ u.loss := mul_nonneg (mul_nonneg (by positivity) v.link) v.mass
theorem err_pos : u.theta ≤ u.err :=
  le_mul_of_one_le_left v.scale.le (one_le_pow₀ (le_add_of_nonneg_right (by positivity)))
theorem error_pos (k : ℕ) : 0 ≤ u.error k := by
  have := v.crude_pos
  have := v.thin
  have := v.loss_pos
  unfold error; positivity

end Valid

theorem cost_succ (k : ℕ) : u.cost (k+1) = u.cost k + (1+4^u.K)*u.tests.value u.K := by
  unfold cost; push_cast; ring

abbrev Scale := Fin u.h → Bool
abbrev Bin := Option (Fin u.J)

def dir (east : Bool) (bin : u.Bin) := if bin.isSome then east else !east

end Dials

namespace Board

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}

structure Stage (tag : Stamp Bit I) (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) : Prop where
  rate : raw.rate = u.rate k
  visible : tag.Visible w rule k (u.a^k)
  capped : tag.Capped rule old (!d) (u.a^k) (u.D k).step u.t
  reliable : rule.Reliable w.place u.K (u.margin k) (u.cost k)

namespace Stage

variable {rule : Rules raw} {old : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid)

def bad (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) :=
  Stamp.bad rule old (!d) (u.a^(k+1)) (u.D k).step

def screened (u : Dials) (k : ℕ) (rule : Rules raw) (old : w.Round) (d : Bool) :=
  rule.screen u.tests (bad u k rule old d)

include G v in
theorem merge : tag.Capped rule old (!d) (u.a^(k+1)) (u.D k).step u.U := by
  rw [pow_succ]; exact G.capped.merge (by have := v.base; omega)

include G in
theorem view : tag.Visible w (screened u k rule old d) k (u.a^(k+1)) := by
  apply Stamp.Visible.screen
  rw [pow_succ]; exact G.visible.enlarge _

include G v in
theorem checked : (screened u k rule old d).Reliable w.place u.K (u.margin k) (u.cost (k+1)) := by
  rw [u.cost_succ]
  exact rule.reliable_screen _ _ G.reliable (fun g s _ hs => ((G.merge v).given g s hs).trans v.crude)

def gate (hk : k ≤ u.h) := (G.checked v).gates (v.reliable k hk) u.tests (bad u k rule old d)
  (fun _ _ h => h.2)

include G v in
theorem crude (hide s : Finset I) (hs : s ⊆ hide) (j : ℕ) (i : I) (hi : w.place i ∈ piece (u.a^(k+1)) j) :
    coin.law.prob (old.Cover (piece (u.a^(k+1)) j) (!d) (u.D k).step
      ((screened u k rule old d).watch hide s) i) ≤ u.U := by
  apply le_trans _ (((G.merge v) hide s hs j).bound i hi)
  apply coin.law.mono
  intro x hc
  exact hc.mono (Finset.sdiff_subset_sdiff (rule.screen_pass ..) Finset.Subset.rfl)

theorem ledger (hk : k < u.h) (j : ℕ) :
    Ledger (G.gate v hk.le) old (piece (u.a^(k+1)) j) d (u.D k) u.M u.A := by
  have h := v.bounds k hk
  have hr : raw.pins.rate ≤ u.p := G.rate.le.trans (v.rate_le k)
  apply Ledger.make v.passage (u.tests.positive _).le v.mass v.link
    ((G.checked v).resample _ _ _ _) h.1 ?_ ?_ ?_
  · apply le_trans _ h.2
    unfold Dials.capacity
    gcongr
  · intro x g hg hn
    rw [← w.home_eq hg]
    exact Stamp.available rule u.tests hn
  · intro i hi
    have hh := G.crude v ∅ ∅ Finset.Subset.rfl j i hi
    apply le_trans _ hh
    apply coin.law.mono
    intro x hc
    simp only [Round.Cover,Rules.watch,Raw.force_empty,Finset.sdiff_empty]
    exact hc

end Stage
end Board
end OAI.Geometry.Hirsch.Layer
end

-- Refinement
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Stage

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}
  {rule : Rules raw} {old mid q : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid) (hk : k < u.h)

def scale (i : I) : u.Scale := (G.ledger v hk (w.place i / u.a^(k+1))).colors u.a u.h u.theta i
def band (mid : w.Round) (i : I) := (G.ledger v hk (w.place i / u.a^(k+1))).band mid i
def pick (mid : w.Round) (i : I) : u.Bin := bucket u.t u.J (raw.pins.mass (G.band v hk mid i))

theorem band_eq {i : I} {j : ℕ} (hi : w.place i ∈ piece (u.a^(k+1)) j) :
    G.band v hk mid i = (G.ledger v hk j).band mid i := by
  change w.place i / u.a^(k+1) = j at hi
  subst j; rfl

theorem key_le (j : ℕ) : (G.ledger v hk j).key ≤ u.key :=
  mul_le_mul_of_nonneg_left (G.rate.le.trans (v.rate_le k)) (by linarith [v.link])

theorem beta_le (j : ℕ) : (G.ledger v hk j).beta ≤ u.beta :=
  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (G.key_le v hk j) _) (by positivity))
    (mul_nonneg (by norm_num) v.mass)

theorem rare (hn : n ≤ u.a^u.h) (hm : mid.Finer old) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) (j : ℕ) (i : I)
    (hi : w.place i ∈ piece (u.a^(k+1)) j) (he : w.Shore d i) :
    raw.pins.mass (((G.ledger v hk j).book mid i (flat (u.D k).limit)).filter
      (fun s => mid.Straddles d s (piece (u.a^(k+1)) j) i)) ≤ u.err := by
  let L := G.ledger v hk j
  have suff : ∀ i, G.scale v hk i = c → w.place i ∈ piece (u.a^(k+1)) j → L.colors u.a u.h u.theta i = c := by
    intro x h hx
    change w.place x / u.a^(k+1) = j at hx
    exact (congrArg (fun z => (G.ledger v hk z).colors u.a u.h u.theta x) hx.symm).trans h
  apply L.straddlers hm (by have := v.base; omega) hn v.scale
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (G.beta_le v hk j) (by norm_num)) v.compare)
    ((add_le_add_left (G.key_le v hk j) _).trans v.discard) (color := c) ?_ hi he
  refine ⟨fun i h => suff _ (hl.east i h),fun i h => ?_⟩
  obtain ⟨y,hy,hm,hv,hh⟩ := hl.west i h
  exact ⟨y,hy,hm,hv,suff _ hh⟩

variable (foil : ∀ j : Fin u.J, Foil coin tag (k+1) raw.pins.rate u.L (price u.t j))

def bars (mid : w.Round) (i : I) : Finset Bit :=
  match G.pick v hk mid i with
  | none => ∅
  | some j => (foil j).bits (G.band v hk mid i)

theorem support (mid : w.Round) (i : I) (b : Bit) (h : b ∈ G.bars v hk foil mid i) :
    ¬tag.pin b ∧ b ∈ tag.scope w (k+1) (u.a^(k+1)) i := by
  unfold bars at h
  split at h
  · simp at h
  · rename_i j _
    let L := G.ledger v hk (w.place i / u.a^(k+1))
    exact (foil j).visible _ i (fun _ hs => L.support rfl (L.band_sub hs)) b h

theorem barrier_bound (mid : w.Round) (i : I) :
    Real.exp (-8*u.L) ≤ coin.weight (G.bars v hk foil mid i) := by
  unfold bars
  split
  · simp [Coins.weight,v.lambda]
  · rename_i j h
    exact (foil j).low _ (bucket_high h).2.le

variable (hf : tag.Fresh fresh k)

def advance (mid : w.Round) := hf.advance G.view (G.bars v hk foil mid) (G.support v hk foil mid)

theorem visible_next (mid : w.Round) : tag.Visible w (G.advance v hk foil hf mid) (k+1) (u.a^(k+1)) :=
  hf.visible G.view _ _

theorem reliable_next (mid : w.Round) :
    (G.advance v hk foil hf mid).Reliable w.place u.K (u.margin (k+1)) (u.cost (k+1)) := by
  rw [Dials.margin,pow_succ (Real.exp _)]
  exact hf.reliable G.view _ _ (Real.exp_pos _) (by simp [v.lambda]) (G.barrier_bound v hk foil mid) (G.checked v)

variable (hide s : Finset I) (hs : s ⊆ hide)

def draw := hf.draw G.view (G.gate v hk.le) rfl hide s hs

theorem thin (x : Table Bit) : (G.advance v hk foil hf mid).watch hide s x ⊆ (G.draw v hk hf hide s hs).thin x :=
  fun g hg => (hf.watched G.view _ rfl hide s hs _ _ x g hg).1

theorem switched (hn : n ≤ u.a^u.h) (hm : mid.Finer old) (hq : q.Finer mid) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) {bin : Fin u.J}
    (hl' : q.Links d (fun i => G.pick v hk mid i = some bin)) (j : ℕ) :
    (G.ledger v hk j).Switched (G.draw v hk hf hide s hs) mid q (fun i => G.pick v hk mid i = some bin)
      ((G.advance v hk foil hf mid).watch hide s) (price u.t bin) u.err (Real.exp (-u.L)) u.U := by
  have hlow := price_low v.tpos bin.val
  have ht := v.tpos
  have key : 0 ≤ u.key := (G.ledger v hk j).positive.2.1.trans (G.key_le v hk j)
  refine ⟨hm,hq,hl',G.thin v hk foil hf hide s hs,G.crude v hide s hs j,G.rare v hk hn hm hl j,
    ?_,(foil bin).positive,?_,?_,(Real.exp_pos _).le,?_⟩
  · intro i hi hp
    rw [← G.band_eq v hk hi]
    exact (bucket_high hp).1
  · change u.err + u.loss ≤ _
    linarith [v.err_pos,v.discard,v.rare]
  · nlinarith [G.beta_le v hk j,v.compare,v.err_pos,v.rare,v.scale]
  intro B hB
  refine ⟨_,(foil bin).high B hB,?_,fun g hh R =>
    (foil bin).independent B (G.visible_next v hk foil hf mid) hide s q _ d R g hh⟩
  intro g hg hp hsub x hx
  have hh := (hf.watched G.view (G.gate v hk.le) rfl hide s hs _ _ x g hx).2
  change All (G.bars v hk foil mid g) x at hh
  rw [bars,hp,G.band_eq v hk hg] at hh
  exact fun b hb => hh _ (Finset.image_mono _ hsub hb)

end OAI.Geometry.Hirsch.Layer.Board.Stage
end

-- Stages
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Stage

open Coins

variable {I Bit : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I] {coin : Coins Bit}
  {raw fresh : coin.Raw I} {n : ℕ} {w : Board I n} {tag : Stamp Bit I} {k : ℕ} {u : Dials}
  {rule : Rules raw} {old mid q : w.Round} {d : Bool}
  (G : Stage tag u k rule old d) (v : u.Valid) (hk : k < u.h)
  (foil : ∀ j : Fin u.J, Foil coin tag (k+1) raw.pins.rate u.L (price u.t j))
  (hf : tag.Fresh fresh k) (hz : fresh.rate = u.z)

include hz in
theorem error_eq (j : ℕ) : (G.ledger v hk j).error u.U fresh.pins.rate = u.error k := by
  change (G.ledger v hk j).error u.U fresh.rate = _
  rw [hz]; rfl

include v hk G in
theorem small : 2*raw.pins.rate + u.error k + u.err + u.K*raw.pins.rate*u.M ≤ u.t/4 := by
  have h : raw.pins.rate ≤ u.p := G.rate.le.trans (v.rate_le k)
  apply le_trans _ (v.small k hk)
  have := v.mass
  gcongr

include hz in
theorem next (hn : n ≤ u.a^u.h) (hm : mid.Finer old) (hq : q.Finer mid) {c : u.Scale}
    (hl : mid.Links d (fun i => G.scale v hk i = c)) {bin : u.Bin}
    (hl' : q.Links d (fun i => G.pick v hk mid i = bin)) :
    Stage tag u (k+1) (G.advance v hk foil hf mid) q (!(u.dir d bin)) := by
  have hr := G.visible_next v hk foil hf mid
  refine ⟨?_,hr,?_,G.reliable_next v hk foil hf mid⟩
  · change raw.rate * fresh.rate = _
    rw [G.rate,hz]; simp [Dials.rate,pow_succ,mul_assoc]
  rw [Bool.not_not]
  apply hr.capped v.tpos.le
  intro hide s hs i
  let j := w.place i / u.a^(k+1)
  let area := piece (u.a^(k+1)) j
  have hi : w.place i ∈ area := rfl
  let L := G.ledger v hk j
  let draw := G.draw v hk hf hide s hs
  let select := (G.advance v hk foil hf mid).watch hide s
  have hthin : ∀ x, select x ⊆ draw.thin x := G.thin v hk foil hf hide s hs
  have herr := G.error_eq v hk hz j
  have small := G.small v hk
  have hpos := v.scale.le.trans v.err_pos
  change coin.law.prob (q.Cover area (u.dir d bin) (u.cycles*(2+(u.D k).max)) select i) ≤ u.t
  cases bin with
  | some b =>
    have h := G.switched v hk foil hf hide s hs hn hm hq hl hl' j
    have hh := h.iterate v.tpos.le hpos v.crude_pos.le (by rw [herr]; exact small) v.contraction u.cycles hi
    exact hh.trans (by linarith [v.stop])
  | none =>
    have bound : ∀ y, G.pick v hk mid y = none → w.Shore d y → w.place y ∈ area →
        coin.law.prob (q.Cover area (!d) (u.D k).max select y) ≤ u.error k + u.t/4 := by
      intro y hy _ hya
      have mass : raw.pins.mass (L.band mid y) ≤ u.M :=
        (raw.pins.mass_mono L.band_sub).trans (L.bound hm hya (fun _ => Ledger.base)).mass
      have low : raw.pins.mass (L.band mid y) ≤ u.t/4 := by
        unfold pick at hy
        rw [G.band_eq v hk hya] at hy
        exact (bucket_low (mass.trans_lt v.bins) hy).le
      have hh := L.neutral draw hm hya (G.crude v hide s hs j y hya)
      rw [herr] at hh
      apply le_trans _ (hh.trans (add_le_add_right low _))
      exact coin.law.mono fun x h => (hq.test le_rfl _ h).mono (hthin x)
    have red := hl'.reduce (!d) hi (fun x => (hthin x).trans (draw.pinned x))
      (add_nonneg (v.error_pos k) (div_nonneg v.tpos.le (by norm_num))) bound
    have hsize : 2+(u.D k).max ≤ u.cycles*(2+(u.D k).max) := Nat.le_mul_of_pos_left _ u.run
    apply le_trans _ (red.trans (show _ ≤ u.t by
      have hh : 0 ≤ (u.K : ℝ)*raw.pins.rate*u.M := mul_nonneg (mul_nonneg (by positivity) raw.pos.le) v.mass
      linarith [v.tpos]))
    exact coin.law.mono fun _ h => Round.test_mono _ _ _ _ (fun _ => hsize) _ h

include v in
theorem initial (hr : tag.Tagged raw 0) (hp : raw.rate = u.p) (r : w.Round) (d : Bool) :
    Stage tag u 0 (Rules.initial raw) r d := by
  have hv : tag.Visible w (Rules.initial raw) 0 (u.a^0) :=
    ⟨hr,by simp [Rules.initial],fun _ _ _ _ => rfl⟩
  refine ⟨by simpa [Dials.rate] using hp,hv,?_,?_⟩
  swap
  · simpa [Dials.margin,Dials.cost] using Rules.initial_reliable raw w.place u.K
  apply hv.capped v.tpos.le
  intro hide s hs i
  let area := w.home (u.a^0) i
  obtain ⟨l,hl,hh⟩ := r.spine (i := i) (area := area) rfl (!d)
  have hsize : l.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro g hg j hj
    have h₁ := hh g (List.mem_toFinset.mp hg)
    have h₂ := hh j (List.mem_toFinset.mp hj)
    apply h₁.unique h₂
    simpa [area,home,piece] using h₁.info.2.1.trans h₂.info.2.1.symm
  have hprob := raw.pins.extra_hit ∅ l.toFinset (Finset.disjoint_empty_right _)
  simp only [Pins.weight,Finset.card_empty,pow_zero,mul_one,Finset.empty_subset,true_and] at hprob
  have hraw : l.toFinset.card * raw.pins.rate ≤ u.t :=
    (mul_le_of_le_one_left raw.pos.le (by exact_mod_cast hsize)).trans (hp.le.trans v.initial_le)
  apply le_trans _ (hprob.trans hraw)
  apply coin.law.mono
  intro x hc
  obtain ⟨g,hg,hm⟩ := hc l hl
  exact ⟨g,List.mem_toFinset.mpr hg,(Rules.initial raw).watch_pin hs x hm⟩

theorem final_path (hn : n ≤ u.a^(k+1)) {g : I} {x : Table Bit}
    (hp : g ∈ (screened u k rule old d).pass x) :
    ∃ j l, ¬w.live j ∧ old.Trip Set.univ g j (flat (u.D k).step) l ∧
      ∀ i ∈ l, i ∈ (screened u k rule old d).pass x → w.place i = w.place g := by
  have hb := ((Rules.mem ..).mp hp).2.2.2.1
  obtain ⟨l,⟨j,he,ht⟩,hh⟩ := Stamp.available rule u.tests hb
  have same : ∀ i, w.place i / u.a^(k+1) = 0 := fun i => Nat.div_eq_of_lt ((w.num_lt true i).trans_le hn)
  have hi : w.place j ∈ w.home (u.a^(k+1)) g := (same j).trans (same g).symm
  exact ⟨j,l,(he.resolve_right fun h => h.1 hi).2,ht.widen (Set.subset_univ _),hh⟩

end OAI.Geometry.Hirsch.Layer.Board.Stage
end

-- Growth
noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth

def E (r : ℕ) (x : ℝ) := Real.exp ((r : ℝ)*Real.log 2*x)

theorem pos (r : ℕ) (x : ℝ) : 0 < E r x := Real.exp_pos _

theorem zero (r : ℕ) : E r 0 = 1 := by simp [E]

theorem one (r : ℕ) : E r 1 = (2 : ℝ)^r := by
  rw [E,mul_one,Real.exp_nat_mul,Real.exp_log (by norm_num)]

theorem mul (r : ℕ) (x y : ℝ) : E r x * E r y = E r (x+y) := by
  unfold E; rw [← Real.exp_add,mul_add]

theorem pow (r : ℕ) (x : ℝ) (k : ℕ) : E r x ^ k = E r (x*k) := by
  unfold E; rw [← Real.exp_nat_mul]; congr 1; ring

theorem nat (r k : ℕ) : (((2^r)^k : ℕ) : ℝ) = E r k := by
  rw [Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,← one,pow,one_mul]

theorem mono (r : ℕ) {x y : ℝ} (h : x ≤ y) : E r x ≤ E r y := by
  unfold E; gcongr

theorem le_one (r : ℕ) {x : ℝ} (h : x ≤ 0) : E r x ≤ 1 := (mono r h).trans_eq (zero r)

theorem dominates {x y : ℝ} (h : x < y) (c : ℝ) :
    ∀ᶠ r : ℕ in atTop, c * E r x < E r y := by
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have gt : 1 < Real.exp (Real.log 2*(y-x)) := Real.one_lt_exp_iff.mpr (mul_pos logpos (sub_pos.mpr h))
  filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt gt).eventually (eventually_gt_atTop c)] with r hr
  rw [← Real.exp_nat_mul,← mul_assoc] at hr
  exact (mul_lt_mul_of_pos_right hr (pos r x)).trans_eq ((mul r (y-x) x).trans (by rw [sub_add_cancel]))

def Order (f : ℕ → ℝ) (x : ℝ) := ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in atTop, |f r| ≤ c*E r x

namespace Order

variable {f g : ℕ → ℝ} {x y : ℝ}

theorem base (x : ℝ) : Order (fun r => E r x) x :=
  ⟨1,one_pos,Eventually.of_forall (fun r => by simp [abs_of_pos (pos r x)])⟩

theorem const (c : ℝ) : Order (fun _ => c) 0 :=
  ⟨|c|+1,by positivity,Eventually.of_forall (fun r => by simp [zero])⟩

theorem up (h : Order f x) (hh : x ≤ y) : Order f y := by
  obtain ⟨c,hc,h⟩ := h
  exact ⟨c,hc,h.mono fun r hr => hr.trans (mul_le_mul_of_nonneg_left (mono r hh) hc.le)⟩

theorem prod (h : Order f x) (hh : Order g y) : Order (fun r => f r*g r) (x+y) := by
  obtain ⟨c,hc,h⟩ := h
  obtain ⟨d,hd,hh⟩ := hh
  refine ⟨c*d,mul_pos hc hd,?_⟩
  filter_upwards [h,hh] with r hr hr'
  rw [abs_mul,← mul,mul_mul_mul_comm]
  exact mul_le_mul hr hr' (abs_nonneg _) (mul_nonneg hc.le (pos r x).le)

theorem scale (h : Order f x) (c : ℝ) : Order (fun r => c*f r) x :=
  ((const c).prod h).up (by simp)

theorem add (h : Order f x) (hh : Order g x) : Order (fun r => f r+g r) x := by
  obtain ⟨c,hc,h⟩ := h
  obtain ⟨d,hd,hh⟩ := hh
  refine ⟨c+d,add_pos hc hd,?_⟩
  filter_upwards [h,hh] with r hr hr'
  rw [add_mul]; exact (abs_add_le ..).trans (add_le_add hr hr')

theorem power (h : Order f x) (k : ℕ) : Order (fun r => f r^k) (x*k) := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c^k,pow_pos hc _,?_⟩
  filter_upwards [h] with r hr
  rw [abs_pow,← pow,← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hr _

theorem lt (h : Order f x) (hh : x < y) : ∀ᶠ r : ℕ in atTop, f r < E r y := by
  obtain ⟨c,_,h⟩ := h
  filter_upwards [h,dominates hh c] with r hr hr'
  exact ((le_abs_self _).trans hr).trans_lt hr'

theorem identity (x : ℝ) (hx : 0 < x) : Order (fun r => (r : ℝ)) x := by
  have h : 0 < Real.log 2*x := mul_pos (Real.log_pos (by norm_num)) hx
  refine ⟨(Real.log 2*x)⁻¹,inv_pos.mpr h,Eventually.of_forall fun r => ?_⟩
  rw [abs_of_nonneg (Nat.cast_nonneg _),inv_mul_eq_div,le_div_iff₀ h]
  unfold E; rw [mul_assoc]
  linarith [Real.add_one_le_exp ((r : ℝ)*(Real.log 2*x))]

end Order

def thresholds (K r : ℕ) (F : ℝ) (hF : 0 ≤ F) : Thresholds K where
  value j := E r (-F*3^(K-j))
  positive _ := pos ..
  mono := by
    intro i j hij
    apply mono
    apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hF)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  ratio := by
    intro j hj
    rw [pow,mul]
    apply mono
    rw [show K-j = K-(j+1)+1 by omega,pow_succ,Nat.sub_self,pow_zero]
    have := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := K-(j+1))) hF
    push_cast
    linarith

end OAI.Geometry.Hirsch.Layer.Growth
end

-- Calibration
noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth

def exponent (K : ℕ) := 100*K*3^K+2

structure Plan where
  K : ℕ
  h : ℕ
  enough : 2 ≤ K

namespace Plan

variable (p : Plan)

def T := exponent p.K
def N := 16*(p.h+1)*p.K
def rounds := p.N*(p.T+1)

theorem two : (2 : ℝ) ≤ p.K := Nat.cast_le.mpr p.enough

theorem large : 100*(p.K : ℝ) ≤ p.T := by
  have h := Nat.le_mul_of_pos_right (100*p.K) (by positivity : 0 < 3^p.K)
  exact_mod_cast (show 100*p.K ≤ p.T by unfold T exponent; omega)

theorem npos : 0 < p.N := by have := p.enough; unfold N; positivity

def dial (r : ℕ) : Dials where
  K := p.K
  a := 2^r
  h := p.h
  J := 4*r+2
  cycles := p.rounds
  run := Nat.mul_pos p.npos (by omega)
  tests := thresholds p.K r (100*p.K) (by positivity)
  p := E r (-2*p.T)
  z := E r (-4/p.K)
  t := E r (-p.T)
  L := r*Real.log 2/p.N
  M := E r (3-p.T)
  A := E r (-32*p.K)
  theta := E r (-(p.T : ℝ)-4*p.K)
  gamma := E r (-1)

theorem aval (r : ℕ) : ((p.dial r).a : ℝ) = E r 1 := by simp [dial,one]
theorem umax (r : ℕ) : (p.dial r).U = E r (1-p.T) := by
  rw [Dials.U,p.aval]; exact mul ..
theorem end_test (r : ℕ) : (p.dial r).tests.value (p.dial r).K = E r (-100*p.K) := by
  simp [dial,thresholds]
theorem lambda (r : ℕ) (x : ℝ) : Real.exp (x*(p.dial r).L) = E r (x/p.N) := by
  unfold dial E; congr 1; ring
theorem neg_lambda (r : ℕ) : Real.exp (-(p.dial r).L) = E r (-1/p.N) := by
  simpa using p.lambda r (-1)

theorem start (r : ℕ) : (p.dial r).U ≤ (p.dial r).tests.value 0 := by
  rw [p.umax]
  apply mono
  simp only [T,exponent,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.sub_zero]
  linarith

theorem order_loss : Order (fun r => (p.dial r).loss) (-(p.T : ℝ)-20*p.K) := by
  exact (((Order.base (-32*p.K)).scale (p.K+1)).prod (Order.base (3-p.T))).up (by linarith [p.two])

theorem order_key : Order (fun r => (p.dial r).key) (-(p.T : ℝ)-20*p.K) := by
  have h := (Order.const 1).add ((Order.base (-32*p.K)).up (by linarith [p.two]))
  exact (h.prod (Order.base (-2*p.T))).up (by linarith [p.large,p.two])

theorem order_beta : Order (fun r => (p.dial r).beta) (-2*p.T-10*p.K) :=
  (((Order.base (3-p.T)).scale 2).prod ((p.order_key.add p.order_loss).scale p.K)).up (by linarith [p.two])

theorem order_err : Order (fun r => (p.dial r).err) (-(p.T : ℝ)-2*p.K) := by
  have hf : Order (fun r => Board.Ledger.factor (p.dial r).a p.h) 2 := by
    have h := (Order.base 1).scale 4
    have hh := (((h.prod h).scale p.h).scale 9).up (by norm_num : (1 : ℝ)+1 ≤ 2)
    have hsum := ((Order.const 1).up (by norm_num : (0 : ℝ) ≤ 2)).add hh
    simpa only [Board.Ledger.factor,Board.Ledger.Box,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_mul,Nat.cast_ofNat,aval] using hsum
  exact ((hf.power p.K).prod (Order.base (-(p.T : ℝ)-4*p.K))).up (by linarith)

theorem order_error (k : ℕ) : Order (fun r => (p.dial r).error k) (-(p.T : ℝ)-1) := by
  have hK : (p.K : ℝ) ≠ 0 := by linarith [p.two]
  have h : Order (fun r => (p.dial r).U) (1-p.T) := by simp only [umax]; exact Order.base _
  have hh := (h.scale ((p.dial 0).capacity k)).prod ((Order.base (-4/p.K)).power p.K)
  exact (hh.up (by rw [div_mul_cancel₀ _ hK]; linarith)).add
    ((p.order_loss.scale (p.K+1)).up (by linarith [p.two]))

theorem small (k : ℕ) : ∀ᶠ r : ℕ in atTop,
    let u := p.dial r
    2*u.p + u.error k + u.err + u.K*u.p*u.M ≤ u.t/4 := by
  have h := Order.base (-2*(p.T : ℝ))
  have h' : -2*(p.T : ℝ) ≤ -(p.T : ℝ)-1 := by linarith [p.large,p.two]
  have lhs := (((h.up h').scale 2).add (p.order_error k)).add (p.order_err.up (by linarith [p.two]))
  have rhs := (h.scale p.K).prod (Order.base (3-p.T))
  have sum := (lhs.add (rhs.up (by linarith [p.large,p.two]))).scale 4
  filter_upwards [sum.lt (show -(p.T : ℝ)-1 < -(p.T : ℝ) by linarith)] with r hr
  change 4*(2*(p.dial r).p + (p.dial r).error k + (p.dial r).err + (p.dial r).K*(p.dial r).p*(p.dial r).M) < (p.dial r).t at hr
  dsimp only; linarith

theorem comparisons : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    3*u.beta < u.theta^2 ∧ u.key+u.loss ≤ u.theta ∧ u.err ≤ u.t/32 := by
  have hb := (p.order_beta.scale 3).lt (y := (-(p.T : ℝ)-4*p.K)*2) (by linarith [p.two])
  have hl := (p.order_key.add p.order_loss).lt (y := -(p.T : ℝ)-4*p.K) (by linarith [p.two])
  have he := (p.order_err.scale 32).lt (y := -(p.T : ℝ)) (by linarith [p.two])
  filter_upwards [hb,hl,he] with r hb hl he
  refine ⟨?_,hl.le,?_⟩
  · change _ < E r _ ^ 2
    rw [pow,Nat.cast_ofNat]; exact hb
  · change 32*(p.dial r).err < (p.dial r).t at he
    linarith

end Plan
end OAI.Geometry.Hirsch.Layer.Growth
end

-- Valid
noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer.Growth.Plan

variable (p : Plan)

theorem bounds (k : ℕ) : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.capacity k*u.U ≤ u.gamma*u.M ∧
    u.capacity k*(u.tests.value u.K+(u.K*(u.D k).max+(u.D k).step+1)*u.p) ≤ u.gamma*u.A := by
  let c : ℝ := (p.dial 0).capacity k
  let b : ℝ := p.K*((p.dial 0).D k).max+((p.dial 0).D k).step+1
  have h := dominates (show 1-(p.T : ℝ) < -1+(3-p.T) by linarith) c
  have h' := ((Order.base (-100*p.K)).add
    (((Order.base (-2*p.T)).scale b).up (by linarith [p.large,p.two]))).scale c
  filter_upwards [h,h'.lt (y := -1+(-32*p.K)) (by linarith [p.two])] with r h h'
  dsimp only
  rw [umax,end_test]
  rw [← mul] at h h'
  exact ⟨h.le,h'.le⟩

theorem reliable (k : ℕ) (hk : k ≤ p.h) : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.gamma ≤ u.margin k^u.K - 2*u.K*u.cost (k+1) := by
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.npos
  have gap : (-1 : ℝ) < (-8/p.N*k)*p.K := by
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,lt_div_iff₀ hN]
    simp only [N,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    have hh : (k : ℝ) ≤ p.h := Nat.cast_le.mpr hk
    nlinarith [p.two,mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg p.K : (0 : ℝ) ≤ p.K)]
  have cost := (((Order.base (-100*p.K)).scale (1+4^p.K)).scale (↑(k+1) : ℝ)).scale (2*p.K)
  have hh := ((Order.base (-1)).add (cost.up (by linarith [p.two]))).lt gap
  filter_upwards [hh] with r hh
  dsimp only; rw [le_sub_iff_add_le,Dials.margin,p.lambda,pow,pow,Dials.cost,p.end_test]
  exact hh.le

theorem contract : ∀ᶠ r : ℕ in atTop, let u := p.dial r
    u.K*Real.exp (-u.L) ≤ 1/2 ∧ (u.K*Real.exp (-u.L))^u.cycles ≤ u.t/2 := by
  have hN : (0 : ℝ) < p.N := Nat.cast_pos.mpr p.npos
  have h := (Order.base (-1/p.N)).scale p.K
  have low := (h.scale 2).lt (div_neg_of_neg_of_pos (by norm_num) hN)
  have gap : (-1/(p.N : ℝ))*p.rounds < -(p.T : ℝ) := by
    rw [rounds,Nat.cast_mul,← mul_assoc,div_mul_cancel₀ _ hN.ne']
    push_cast; linarith
  filter_upwards [low,((h.power p.rounds).scale 2).lt gap] with r hl hh
  rw [zero] at hl
  dsimp only; rw [p.neg_lambda]
  change p.K*E r _ ≤ 1/2 ∧ (p.K*E r _)^p.rounds ≤ E r (-p.T)/2
  constructor <;> linarith

theorem bins (r : ℕ) (hr : 0 < r) : (p.dial r).M < price (p.dial r).t (p.dial r).J := by
  have he : (2 : ℝ)^(4*r+2) = E r 4 * 4 := by
    rw [pow_add,Nat.mul_comm 4 r,pow_mul,← one,pow]; norm_num
  change E r (3-p.T) < E r (-p.T)/4 * 2^(4*r+2)
  rw [he,show E r (-p.T)/4 * (E r 4*4) = E r (-p.T)*E r 4 by ring,mul]
  apply Real.exp_lt_exp.mpr
  apply mul_lt_mul_of_pos_left (by linarith)
  exact mul_pos (Nat.cast_pos.mpr hr) (Real.log_pos (by norm_num))

theorem valid : ∀ᶠ r : ℕ in atTop, (p.dial r).Valid := by
  have hrel := Filter.eventually_all_finite (Set.finite_le_nat p.h) |>.mpr (fun k hk => p.reliable k hk)
  have hbounds := Filter.eventually_all_finite (Set.finite_lt_nat p.h) |>.mpr (fun k _ => p.bounds k)
  have hsmall := Filter.eventually_all_finite (Set.finite_lt_nat p.h) |>.mpr (fun k _ => p.small k)
  filter_upwards [eventually_gt_atTop 0,hrel,hbounds,hsmall,p.comparisons,p.contract] with r hr hrel hb hs he hc
  refine ⟨p.enough,?_,pos ..,mono _ ?_,le_one _ ?_,pos ..,le_one _ ?_,?_,(pos ..).le,
    (pos ..).le,pos ..,pos ..,p.start r,hrel,hb,he.1,he.2.1,he.2.2,p.bins r hr,hs,hc.1,hc.2⟩
  · exact Nat.le_self_pow hr.ne' 2
  · linarith [p.large,p.two]
  · exact neg_nonpos.mpr (Nat.cast_nonneg _)
  · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg _)
  · change 0 ≤ (r : ℝ)*Real.log 2/p.N
    positivity

end OAI.Geometry.Hirsch.Layer.Growth.Plan
end

-- Sizing
noncomputable section

open Filter

namespace OAI.Geometry.Hirsch.Layer

def Dials.count (u : Dials) := (2^u.h * (u.J+1))^u.h

namespace Growth.Plan

variable (p : Plan)

theorem count : ∀ᶠ r : ℕ in atTop, 2*((p.dial r).count : ℝ) ≤ E r 1 := by
  let x := 1/((p.h : ℝ)+1)
  have pos : 0 < x := by unfold x; positivity
  have gap : x*p.h < 1 := by
    unfold x; rw [div_mul_eq_mul_div,div_lt_one (by positivity)]; linarith
  have h := ((Order.identity x pos).scale 4).add ((Order.const 3).up pos.le)
  have hh := (((h.scale (2^p.h)).power p.h).scale 2).lt gap
  filter_upwards [hh] with r hr
  simp only [Dials.count,dial,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
  rw [show (4 : ℝ)*r+2+1 = 4*r+3 by ring]; exact hr.le

theorem bits : ∀ᶠ r : ℕ in atTop, 4*(r*p.h) ≤ 2^r := by
  have h := ((Order.identity (1/2) (by norm_num)).scale (4*p.h)).lt (y := 1) (by norm_num)
  filter_upwards [h] with r hr
  rw [one] at hr
  exact_mod_cast (show (4 : ℝ)*(r*p.h) ≤ 2^r by linarith)

def forMoves (m : ℕ) (hm : 0 < m) : Plan := ⟨64*m,32*exponent (64*m)*m,by omega⟩

theorem final_rate {m : ℕ} (hm : 0 < m) (r : ℕ) :
    let p := forMoves m hm
    (p.dial r).rate p.h = E r (-4*p.T) := by
  let p := forMoves m hm
  have he : (p.h : ℝ) = 32*p.T*m := by simp [p,forMoves,T]
  have hk : (p.K : ℝ) = 64*m := by simp [p,forMoves]
  have hpos : (m : ℝ) ≠ 0 := by positivity
  change E r (-2*p.T)*E r (-4/p.K)^p.h = E r (-4*p.T)
  rw [pow,mul,he,hk]; congr 1; field_simp; ring

end Growth.Plan

theorem Dials.choose (m : ℕ) (hm : 0 < m) :
    ∃ (u : Dials) (b bits chance : ℕ), u.Valid ∧ 2 ≤ b ∧ 0 < bits ∧ 0 < chance ∧
      b^m = u.a^u.h ∧ b^m ≤ 2^bits ∧ (2*chance)*(bits*2) ≤ b ∧
      2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2 := by
  let p := Growth.Plan.forMoves m hm
  obtain ⟨r,hr,hv,hc,hbits⟩ := ((eventually_gt_atTop 0).and (p.valid.and (p.count.and p.bits))).exists
  let u := p.dial r
  have hT : 0 < p.T := by unfold Growth.Plan.T Growth.exponent; omega
  have hh : p.h = 32*p.T*m := rfl
  have he : ((2^r)^(32*p.T))^m = (2^r)^p.h := by rw [hh,pow_mul (2^r) (32*p.T) m]
  refine ⟨u,(2^r)^(32*p.T),r*p.h,(2^r)^(12*p.T),hv,?_,by rw [hh]; positivity,by positivity,he,?_,?_,?_⟩
  · exact (Nat.le_self_pow hr.ne' 2).trans (Nat.le_self_pow (by omega) _)
  · rw [he,pow_mul]
  · calc
      _ = (2^r)^(12*p.T)*(4*(r*p.h)) := by ring
      _ ≤ (2^r)^(12*p.T)*2^r := Nat.mul_le_mul_left _ hbits
      _ ≤ _ := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by positivity) (by omega)
  · apply hc.trans
    change Growth.E r 1 ≤ (((2^r)^(12*p.T) : ℕ) : ℝ)*Growth.E r (-1)*((p.dial r).rate p.h)^2
    rw [Growth.Plan.final_rate hm r,Growth.nat,Growth.pow,Growth.mul,Growth.mul]
    apply Growth.mono
    change 1 ≤ (↑(12*p.T) : ℝ) + -1 + -4*p.T*↑(2 : ℕ)
    push_cast
    linarith [p.two,p.large]

end OAI.Geometry.Hirsch.Layer
end

-- Stock
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Dials

variable (u : Dials)

def History : ℕ → Type
  | 0 => Unit
  | k+1 => (History k × u.Scale) × u.Bin

instance histories (k : ℕ) : Fintype (u.History k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((u.History k × u.Scale) × u.Bin))

theorem card_history (k : ℕ) : Fintype.card (u.History k) = (2^u.h*(u.J+1))^k := by
  induction k with
  | zero => change Fintype.card Unit = 1; exact Fintype.card_unique
  | succ k ih =>
    change Fintype.card ((u.History k × u.Scale) × u.Bin) = _
    simp [ih,Scale,Bin,pow_succ,mul_assoc]

abbrev Ticket := Σ k : Fin u.h, (u.History k × u.Scale) × Option u.Bin

def ticket {k : ℕ} (hk : k < u.h) (prev : u.History k) (c : u.Scale) (bin : Option u.Bin) : u.Ticket :=
  ⟨⟨k,hk⟩,(prev,c),bin⟩

def phase (a : u.Ticket) := 2*a.1.val + if a.2.2.isSome then 1 else 0

theorem phase_lt (a : u.Ticket) : u.phase a < 2*u.h := by
  have := a.1.isLt; unfold phase; split <;> omega

def east : ∀ k, u.History k → Bool
  | 0,_ => true
  | k+1,c => !(u.dir (east k c.1.1) c.2)

def side (a : u.Ticket) := u.east a.1 a.2.1.1

abbrev Cell (I : Type) := Fin (u.h+1) × (I ⊕ (Fin u.J × Finset I))

variable {I : Type} [Fintype I]

def stamp : Stamp (u.Cell I) I where
  age b := b.1
  keys b := b.2.elim (fun i => {i}) Prod.snd
  pin b := b.2.isLeft

def bias (b : u.Cell I) : ℝ :=
  match b.2 with
  | .inl _ => if b.1.val = 0 then u.p else u.z
  | .inr (j,s) => Real.exp ((-4*u.L/price u.t j)*u.rate (b.1.val-1)^s.card)

variable {u} (v : u.Valid)

def Valid.coin : Coins (u.Cell I) where
  bias := u.bias
  pos := by
    rintro ⟨k,i | ⟨j,s⟩⟩
    · simp only [bias]; split <;> first | exact v.initial | exact v.thin
    · exact Real.exp_pos _
  le_one := by
    rintro ⟨k,i | ⟨j,s⟩⟩
    · simp only [bias]; split <;> first | exact v.initial_le.trans v.target | exact v.thin_le
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonpos_of_nonneg _ (pow_nonneg (v.rate_pos _).le _)
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [v.lambda]) (by linarith [price_low v.tpos j.val,v.tpos])

namespace Valid

def atom (k : Fin (u.h+1)) : (v.coin (I := I)).Raw I where
  bits i := {(k,.inl i)}
  rate := if k.val = 0 then u.p else u.z
  pos := by split <;> first | exact v.initial | exact v.thin
  weight i := by simp [Coins.weight,coin,bias]
  unique i j h := by simp [h]

omit [Fintype I] in
theorem tagged (k : Fin (u.h+1)) : u.stamp.Tagged (v.atom (I := I) k) k.val := by
  intro i b hb
  obtain rfl := Finset.mem_singleton.mp hb
  exact ⟨rfl,le_rfl,rfl⟩

def fresh {k : ℕ} (hk : k < u.h) := v.atom (I := I) ⟨k+1,by omega⟩

omit [Fintype I] in
theorem fresh_tag {k : ℕ} (hk : k < u.h) : u.stamp.Fresh (v.fresh (I := I) hk) k :=
  ⟨v.tagged _,fun _ _ hb => by rw [Finset.mem_singleton.mp hb]; rfl⟩

def foil {k : ℕ} (hk : k < u.h) {r : ℝ} (he : r = u.rate k) (j : Fin u.J) :
    Foil (v.coin (I := I)) u.stamp (k+1) r u.L (price u.t j) where
  index s := (⟨k+1,by omega⟩,.inr (j,s))
  age _ := rfl
  keys _ := rfl
  barrier _ := by simp [stamp]
  bias _ := by simp [coin,bias,he]
  positive := by linarith [price_low v.tpos j.val,v.tpos]
  nonneg := v.lambda

end Valid
end OAI.Geometry.Hirsch.Layer.Dials
end

-- Network
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

structure Network (u : Dials) (I : Type) where
  w : Board I (u.a^u.h)
  slot : u.Ticket → I → I
  same : ∀ a i, w.layer (slot a i) = w.layer i
  jump : ∀ a i, slot a i ≠ i → w.live i ∧ w.rank (slot a i) < w.rank i

namespace Network

variable {u : Dials} {I : Type} (Q : Network u I)

def first : Q.w.Round where
  mark i _ := Q.w.Middle i ∧ Q.w.live i
  middle _ _ h := h
  jump _ _ _ := False
  localJump _ _ _ h := h.elim

def refine (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) : Q.w.Round where
  mark i e := r.mark i e ∧ (if e = u.side a then P (Q.w.step i e)
    else Q.w.live (Q.slot a i) ∧ P (Q.w.step (Q.slot a i) (u.side a)))
  middle i e h := r.middle i e h.1
  jump i e j := r.jump i e j ∨ e = !(u.side a) ∧ Q.slot a i = j ∧ j ≠ i
  localJump := by
    rintro i e j (h | ⟨_,rfl,hn⟩)
    · exact r.localJump _ _ _ h
    · exact ⟨(Q.jump a i hn).1,Q.same a i,(Q.jump a i hn).2⟩

theorem finer (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) : (Q.refine r a P).Finer r :=
  ⟨fun _ _ h => h.1,fun _ _ _ h => .inl h⟩

theorem links (r : Q.w.Round) (a : u.Ticket) (P : I → Prop) :
    (Q.refine r a P).Links (u.side a) P := by
  constructor
  · intro i h; simpa [refine] using h.2
  intro i h
  have hh : Q.w.live (Q.slot a i) ∧ P (Q.w.step (Q.slot a i) (u.side a)) := by simpa using h.2
  have hmid := (r.middle _ _ h.1).1
  refine ⟨Q.slot a i,?_,by simpa [Board.Middle,Q.same] using hmid,hh⟩
  by_cases he : Q.slot a i = i
  · exact .inl he
  · exact .inr (.inr ⟨rfl,rfl,he⟩)

variable [Fintype I] (v : u.Valid)

structure Process (k : ℕ) (c : u.History k) where
  raw : (v.coin (I := I)).Raw I
  rule : Coins.Rules raw
  round : Q.w.Round
  stage : Board.Stage u.stamp u k rule round (u.east k c)

namespace Process

variable {Q v} {k : ℕ} {c : u.History k} (g : Q.Process v k c) (hk : k < u.h) (s : u.Scale) (b : u.Bin)

def mid := Q.refine g.round (u.ticket hk c s none) (fun i => g.stage.scale v hk i = s)

def last := Q.refine (g.mid hk s) (u.ticket hk c s (some b)) (fun i => g.stage.pick v hk (g.mid hk s) i = b)

def succ : Q.Process v (k+1) ((c,s),b) where
  raw := g.raw.join (v.fresh hk) ((v.fresh_tag hk).separate g.stage.view)
  rule := g.stage.advance v hk (v.foil hk g.stage.rate) (v.fresh_tag hk) (g.mid hk s)
  round := g.last hk s b
  stage := g.stage.next v hk _ _ rfl le_rfl (Q.finer ..) (Q.finer ..) (Q.links ..) (Q.links ..)

def checked := Board.Stage.screened u k g.rule g.round (u.east k c)

end Process

def process : ∀ k, k ≤ u.h → (c : u.History k) → Q.Process v k c
  | 0,_,_ => ⟨v.atom 0,Coins.Rules.initial _,Q.first,Board.Stage.initial v (v.tagged 0) rfl _ _⟩
  | k+1,hk,c => (process k (by omega) c.1.1).succ (by omega) c.1.2 c.2

def want (a : u.Ticket) (i : I) :=
  let hk := a.1.isLt
  let g := Q.process v a.1.val hk.le a.2.1.1
  match a.2.2 with
  | none => g.stage.scale v hk i = a.2.1.2
  | some b => g.stage.pick v hk (g.mid hk a.2.1.2) i = b

def done (c : u.History u.h) := Q.process v u.h le_rfl c

def passes (c : u.History u.h) (x : Table (u.Cell I)) (i : I) := i ∈ (Q.done v c).checked.pass x

theorem pair (c : u.History u.h) {i j : I} (hi : Q.w.place i = Q.w.place j) (hne : i ≠ j) :
    u.gamma*(u.rate u.h)^2 ≤ v.coin.law.prob (fun x => Q.passes v c x i ∧ Q.passes v c x j) := by
  let g := Q.done v c
  have card : ({i,j} : Finset I).card = 2 := by simp [hne]
  have hh := (g.stage.checked v).passage (s := {i,j}) (card.le.trans v.keys) (by
    intro k hk; left; intro l hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk hl
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> simp [hi]) (v.reliable _ le_rfl)
  change u.gamma*g.raw.rate^({i,j} : Finset I).card ≤ _ at hh
  rw [g.stage.rate,card] at hh
  exact hh.trans (v.coin.law.mono fun _ h => ⟨h (by simp),h (by simp)⟩)

end Network
end OAI.Geometry.Hirsch.Layer.Board
end

-- Agreement
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {X Y Z : Type} (Q : Network u X) (Q' : Network u Y) (f : X → Y) (p : ℕ)

def Agree : ℕ → X → Prop
  | 0,_ => True
  | R+1,i => Q.w.layer i = Q'.w.layer (f i) ∧ (Q.w.live i ↔ Q'.w.live (f i)) ∧
      (∀ d, Q.w.live i → f (Q.w.step i d) = Q'.w.step (f i) d ∧ Agree R (Q.w.step i d)) ∧
      ∀ a, u.phase a < p → f (Q.slot a i) = Q'.slot a (f i) ∧ Agree R (Q.slot a i)

variable {Q Q' f p} {R S : ℕ} {i : X}

theorem Agree.less (h : Q.Agree Q' f p R i) {q : ℕ} (hq : q ≤ p) (hs : S ≤ R) : Q.Agree Q' f q S i := by
  induction S generalizing R i with
  | zero => exact True.intro
  | succ s ih =>
    cases R with
    | zero => omega
    | succ r =>
      exact ⟨h.1,h.2.1,fun d hl => ⟨(h.2.2.1 d hl).1,ih (h.2.2.1 d hl).2 (by omega)⟩,
        fun a ha => ⟨(h.2.2.2 a (ha.trans_le hq)).1,ih (h.2.2.2 a (ha.trans_le hq)).2 (by omega)⟩⟩

theorem Agree.cut (h : Q.Agree Q' f p R i) (hs : S ≤ R) : Q.Agree Q' f p S i := h.less le_rfl hs

theorem Agree.symm {e : X ≃ Y} (h : Q.Agree Q' e p R i) : Q'.Agree Q e.symm p R (e i) := by
  induction R generalizing i with
  | zero => exact True.intro
  | succ R ih =>
    simp only [Agree,Equiv.symm_apply_apply]
    refine ⟨h.1.symm,h.2.1.symm,?_,?_⟩
    · intro d hl
      obtain ⟨he,hh⟩ := h.2.2.1 d (h.2.1.mpr hl)
      rw [← he]; exact ⟨e.symm_apply_apply _,ih hh⟩
    · intro a ha
      obtain ⟨he,hh⟩ := h.2.2.2 a ha
      rw [← he]; exact ⟨e.symm_apply_apply _,ih hh⟩

theorem Agree.place (h : Q.Agree Q' f p (R+1) i) : Q.w.place i = Q'.w.place (f i) := congrArg (· / 3) h.1

theorem Agree.shore (h : Q.Agree Q' f p (R+1) i) (d : Bool) : Q.w.Shore d i ↔ Q'.w.Shore d (f i) := by
  simp only [Shore,h.1]

theorem Agree.num (h : Q.Agree Q' f p (R+1) i) (d : Bool) : Q.w.num d i = Q'.w.num d (f i) := by
  simp only [Board.num,loc,h.1]

def Fits (Q : Network u X) (p : ℕ) (r : Q.w.Round) :=
  ∀ i d j, r.jump i d j → ∃ a, u.phase a < p ∧ d = !(u.side a) ∧ Q.slot a i = j

theorem Fits.refine {r : Q.w.Round} (h : Q.Fits p r) {a : u.Ticket} (ha : u.phase a < p) (P : X → Prop) :
    Q.Fits p (Q.refine r a P) := by
  rintro i d j (hh | ⟨he,hj,_⟩)
  · exact h _ _ _ hh
  · exact ⟨a,ha,he,hj⟩

structure Matches (Q : Network u X) (Q' : Network u Y) (e : X ≃ Y) (p R : ℕ)
    (r : Q.w.Round) (r' : Q'.w.Round) : Prop where
  fits : Q.Fits p r
  fits' : Q'.Fits p r'
  mark : ∀ i, Q.Agree Q' e p R i → ∀ d, r.mark i d ↔ r'.mark (e i) d
  jump : ∀ i, Q.Agree Q' e p R i → ∀ d j, r.jump i d j ↔ r'.jump (e i) d (e j)

namespace Matches

variable {e : X ≃ Y} {r : Q.w.Round} {r' : Q'.w.Round} (m : Q.Matches Q' e p R r r')

theorem first : Q.Matches Q' e p 1 Q.first Q'.first :=
  ⟨fun _ _ _ h => h.elim,fun _ _ _ h => h.elim,fun _ h _ => by simp [Network.first,Middle,h.1,h.2.1],by simp [Network.first]⟩

include m

theorem symm : Q'.Matches Q e.symm p R r' r := by
  refine ⟨m.fits',m.fits,?_,?_⟩
  · intro i h d; simpa using (m.mark _ h.symm d).symm
  · intro i h d j; simpa using (m.jump _ h.symm d (e.symm j)).symm

theorem up (h : R ≤ S) : Q.Matches Q' e p S r r' :=
  ⟨m.fits,m.fits',fun i hi => m.mark i (hi.cut h),fun i hi => m.jump i (hi.cut h)⟩

theorem refine {a : u.Ticket} (ha : u.phase a < p) {P : X → Prop} {P' : Y → Prop}
    (hP : ∀ i, Q.Agree Q' e p S i → (P i ↔ P' (e i))) (hle : R ≤ S+2) :
    Q.Matches Q' e p (S+2) (Q.refine r a P) (Q'.refine r' a P') := by
  refine ⟨m.fits.refine ha P,m.fits'.refine ha P',?_,?_⟩
  · intro i h d
    have hm := m.mark _ (h.cut hle) d
    by_cases hc : r.mark i d
    swap
    · simp [Network.refine,hc,mt hm.mpr hc]
    have hs := h.2.2.2 a ha
    simp only [Network.refine,hc,hm.mp hc,true_and]
    split
    · obtain ⟨he,hh⟩ := h.2.2.1 d (r.middle _ _ hc).2
      rw [← he]; exact hP _ (hh.cut (Nat.le_succ _))
    · rw [← hs.1,← hs.2.2.1]
      by_cases hl : Q.w.live (Q.slot a i)
      · obtain ⟨he,hh⟩ := hs.2.2.2.1 (u.side a) hl
        rw [← he,hP _ hh]
      · simp [hl]
  · intro i h d j
    simp only [Network.refine,← (h.2.2.2 a ha).1,e.injective.eq_iff,ne_eq,m.jump _ (h.cut hle)]

theorem step {d : Bool} {j : X} (hm : r.Move i d j) (h : Q.Agree Q' e p (S+1) i) (hR : R ≤ S+1) :
    r'.Move (e i) d (e j) ∧ Q.Agree Q' e p S j := by
  rcases hm with ⟨hl,rfl | hj⟩
  · exact ⟨⟨h.2.1.mp hl,.inl (h.2.2.1 d hl).1⟩,(h.2.2.1 d hl).2⟩
  obtain ⟨a,ha,_,he⟩ := m.fits _ _ _ hj
  exact ⟨⟨h.2.1.mp hl,.inr ((m.jump _ (h.cut hR) _ _).mp hj)⟩,he ▸ (h.2.2.2 a ha).2⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- LocalTests
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

def size (u : Dials) := u.a^u.h*3

def total (u : Dials) (b : Budget) := ∑ j ∈ Finset.range (size u), b j

theorem total_le (u : Dials) {b : Budget} {k : ℕ} (h : b ≤ flat k) : total u b ≤ size u*k := by
  apply le_trans (Finset.sum_le_sum fun j _ => h j)
  simp [flat]

theorem total_spend {u : Dials} {b c : Budget} {j : ℕ} (hj : j < size u) (h : atLayer j + b ≤ c) :
    total u b + 1 ≤ total u c := by
  have hh := Finset.sum_le_sum (s := Finset.range (size u)) (fun i _ => h i)
  simp only [Pi.add_apply,Finset.sum_add_distrib,atLayer,Finset.sum_ite_eq',Finset.mem_range,hj,↓reduceIte] at hh
  exact (Nat.add_comm ..).le.trans hh

variable {u : Dials} {X Y : Type} {Q : Network u X} {Q' : Network u Y} {e : X ≃ Y}
  {p R S : ℕ} {r : Q.w.Round} {r' : Q'.w.Round} {i j : X} {area : Set ℕ} {d : Bool}
  {b : Budget} {l : List X}

namespace Matches

variable (m : Q.Matches Q' e p R r r')
include m

theorem trip (ht : r.Trip area i j b l) (hR : R ≤ S) (h : Q.Agree Q' e p (S+total u b) i) :
    r'.Trip area (e i) (e j) b (l.map e) ∧ Q.Agree Q' e p S j ∧ ∀ g ∈ l, Q.Agree Q' e p S g := by
  induction ht with
  | nil => exact ⟨.nil,h.cut (by omega),by simp⟩
  | @go i j k d b a path hi hm ha ht ih =>
    have cost := total_spend (u := u) (Q.w.bound i) ha
    have hh := h.cut (show S+total u a+1 ≤ S+total u b by omega)
    obtain ⟨hm',hj⟩ := m.step hm hh (by omega)
    obtain ⟨ht,hk,hg⟩ := ih hj
    have mark := m.mark _ (h.cut (by omega)) d
    have key := hh.2.2.1 d hm.1
    have charge : (r.charge i d).map e = r'.charge (e i) d := by
      simp only [Round.charge,mark]; split <;> simp [key.1]
    rw [List.map_append,charge]
    refine ⟨.go (hh.place ▸ hi) hm' (hh.1 ▸ ha) ht,hk,fun g h => ?_⟩
    rcases List.mem_append.mp h with h | h
    · rw [(r.charge_mem.mp h).2]; exact key.2.cut (by omega)
    · exact hg _ h

theorem test (ht : l ∈ r.test area d b i) (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i) :
    l.map e ∈ r'.test area d b (e i) ∧ ∀ g ∈ l, Q.Agree Q' e p (S+1) g := by
  obtain ⟨j,he,ht⟩ := ht
  obtain ⟨ht,hj,hg⟩ := m.trip ht hR h
  exact ⟨⟨e j,by simpa only [Round.Ends,hj.place,hj.2.1,hj.shore] using he,ht⟩,hg⟩

theorem covers {s : Finset X} {t : Finset Y} (hR : R ≤ S+1)
    (h : Q.Agree Q' e p (S+1+total u b) i)
    (hp : ∀ g, Q.Agree Q' e p (S+1) g → (g ∈ s ↔ e g ∈ t)) :
    (r.test area d b i).Covers s ↔ (r'.test area d b (e i)).Covers t := by
  constructor
  · intro hc l hl
    obtain ⟨hl',hh⟩ := m.symm.test hl hR h.symm
    rw [e.symm_apply_apply] at hl'
    obtain ⟨g,hg,hs⟩ := hc _ hl'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    have h' := (hp _ (hh j hj).symm).mp hs
    exact ⟨j,hj,by simpa using h'⟩
  · intro hc l hl
    obtain ⟨hl',hh⟩ := m.test hl hR h
    obtain ⟨g,hg,hs⟩ := hc _ hl'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    exact ⟨j,hj,(hp _ (hh j hj)).mpr hs⟩

theorem minimal {s : Finset X} (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i)
    (hm : (r.test area d b i).Minimal s) : (r'.test area d b (e i)).Minimal (s.map e.toEmbedding) := by
  intro t ht hc
  let a := t.map e.symm.toEmbedding
  have sub : a ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun j hj => ?_,?_⟩
    · have : e j ∈ t := by simpa [a] using hj
      simpa using ht.subset this
    · intro he
      have := Finset.card_lt_card ht
      have := congrArg Finset.card he
      simp only [a,Finset.card_map] at *; omega
  exact hm a sub ((m.covers hR h (fun _ _ => by simp [a])).mpr hc)

theorem support {s : Finset X} (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i)
    (hc : (r.test area d b i).Covers s) (hm : (r.test area d b i).Minimal s) :
    ∀ g ∈ s, Q.Agree Q' e p (S+1) g := by
  intro g hg
  obtain ⟨l,t,hh,_⟩ := hm.essential hc hg
  exact (m.test hh hR h).2 _ (by simp)

theorem on (ho : r.On area d i j) (h : Q.Agree Q' e p (R+1+size u) i) : r'.On area d (e i) (e j) := by
  obtain ⟨v,hr,hv,hm,rfl⟩ := ho
  have ray : ∀ i, Q.w.Ray area d i v → Q.Agree Q' e p (R+1+(Q.w.loc d v-Q.w.loc d i)) i →
      Q'.w.Ray area d (e i) (e v) ∧ Q.Agree Q' e p (R+1) v := by
    clear hr hv hm
    intro i ht
    induction ht with
    | self => exact fun h => ⟨.self,h.cut (by omega)⟩
    | @go i j hi hl ht ih =>
      intro h
      have := ht.forward
      have := Q.w.loc_step d hl
      have hh := h.cut (show R+1+(Q.w.loc d j-Q.w.loc d (Q.w.step i d))+1 ≤ _ by omega)
      obtain ⟨he,hj⟩ := hh.2.2.1 d hl
      obtain ⟨ht,hv⟩ := ih hj
      exact ⟨.go (hh.place ▸ hi) (hh.2.1.mp hl) (he ▸ ht),hv⟩
  have small : Q.w.loc d v ≤ size u := by
    have := Q.w.bound v
    unfold size loc; split <;> omega
  obtain ⟨ht,hh⟩ := ray _ hr (h.cut (by omega))
  exact ⟨e v,ht,hh.place ▸ hv,(m.mark _ (hh.cut (by omega)) _).mp hm,(hh.2.2.1 _ (r.middle _ _ hm).2).1.symm⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- Relabel
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Dials

variable {I : Type} (u : Dials) (e : Equiv.Perm I)

def cells : Equiv.Perm (u.Cell I) :=
  (Equiv.refl _).prodCongr (e.sumCongr ((Equiv.refl _).prodCongr e.finsetCongr))

def tables := (u.cells e).arrowCongr (Equiv.refl Bool)

theorem tables_apply (x : Table (u.Cell I)) (b : u.Cell I) : u.tables e x (u.cells e b) = x b := by
  simp [tables,Equiv.arrowCongr_apply]

theorem tables_id (x : Table (u.Cell I)) : u.tables (Equiv.refl I) x = x := by
  have h : u.cells (Equiv.refl I) = Equiv.refl _ := by
    apply Equiv.ext
    rintro ⟨k,i | ⟨j,s⟩⟩ <;> simp [cells]
  ext; simp [tables,h]

theorem bias_cells (b : u.Cell I) : u.bias (u.cells e b) = u.bias b := by
  rcases b with ⟨k,i | ⟨j,s⟩⟩
  · rfl
  · change Real.exp (_ * _ ^ (s.map e.toEmbedding).card) = _
    rw [Finset.card_map]; rfl

variable [Fintype I] {u} (v : u.Valid)

theorem Valid.invariant (E : Table (u.Cell I) → Prop) :
    v.coin.law.prob (fun x => E (u.tables e x)) = v.coin.law.prob E := by
  apply Law.preserve
  intro x
  change (∏ b, (v.coin.bit b).mass (u.tables e x b)) = ∏ b, (v.coin.bit b).mass (x b)
  rw [← Equiv.prod_comp (u.cells e)]
  simp only [tables_apply,Coins.bit,Valid.coin,bias_cells]

theorem Valid.atom_same (k : Fin (u.h+1)) (i : I) (x : Table (u.Cell I)) :
    i ∈ (v.atom k).pins.success x ↔ e i ∈ (v.atom k).pins.success (u.tables e x) := by
  simp only [Coins.Raw.mem,Valid.atom,Coins.All,Finset.mem_singleton,forall_eq]
  exact iff_of_eq (congrArg (· = true) (u.tables_apply e x (k,.inl i)).symm)

end OAI.Geometry.Hirsch.Layer.Dials

namespace OAI.Geometry.Hirsch.Layer.Pins

variable {I Ω : Type} [Fintype Ω] {p : Law Ω} {pins pins' : Pins p I}
  {e : Equiv.Perm I} {f : Equiv.Perm Ω}

structure Equivariant (pins pins' : Pins p I) (e : Equiv.Perm I) (f : Equiv.Perm Ω) : Prop where
  rate : pins.rate = pins'.rate
  law : ∀ E, p.prob (fun x => E (f x)) = p.prob E
  success : ∀ i x, i ∈ pins.success x ↔ e i ∈ pins'.success (f x)

namespace Equivariant

variable (h : pins.Equivariant pins' e f)
include h

theorem weight (s : Finset I) : pins.weight s = pins'.weight (e.finsetCongr s) := by
  simp [Pins.weight,h.rate]

theorem mass (B : Finset (Finset I)) : pins.mass B = pins'.mass (e.finsetCongr.finsetCongr B) := by
  simp only [Pins.mass,Equiv.finsetCongr_apply,Finset.sum_map]
  exact Finset.sum_congr rfl fun s _ => h.weight s

theorem subset (s : Finset I) (x : Ω) :
    s ⊆ pins.success x ↔ e.finsetCongr s ⊆ pins'.success (f x) := by
  constructor
  · intro h' j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact (h.success _ _).mp (h' hi)
  · exact fun hh i hi => (h.success _ _).mpr (hh (by simpa using hi))

theorem given {E E' : Ω → Prop} (he : ∀ x, E x ↔ E' (f x)) (s : Finset I) :
    pins.given E s = pins'.given E' (e.finsetCongr s) := by
  unfold Pins.given Pins.joint
  rw [h.weight,← h.law (fun x => E' x ∧ e.finsetCongr s ⊆ pins'.success x)]
  exact congrArg (· / _) (p.eq_prob fun x => and_congr (he x) (h.subset s x))

theorem screen {K : ℕ} (t : Thresholds K) {E E' : Ω → Prop} (he : ∀ x, E x ↔ E' (f x)) (x : Ω) :
    pins.Screen t E x ↔ pins'.Screen t E' (f x) := by
  unfold Screen Compatible
  rw [he x]
  apply and_congr_right
  intro _
  constructor
  · intro hh s hs hk
    obtain ⟨s,rfl⟩ := e.finsetCongr.surjective s
    have card : (e.finsetCongr s).card = s.card := Finset.card_map _
    rw [card,← h.given he]
    exact hh _ ((h.subset _ x).mpr hs) (card ▸ hk)
  · intro hh s hs hk
    have card : (e.finsetCongr s).card = s.card := Finset.card_map _
    rw [h.given he s,← card]
    exact hh _ ((h.subset _ x).mp hs) (card.symm ▸ hk)

end Equivariant
end OAI.Geometry.Hirsch.Layer.Pins
end

-- LocalBooks
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I Ω : Type} [Fintype I] [Fintype Ω] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p R S : ℕ} {r : Q.w.Round} {r' : Q'.w.Round} {i : I} {area : Set ℕ} {d : Bool}
  {law : Law Ω} {pins pins' : Pins law I} {K : ℕ} {gamma alpha : ℝ}
  {g : Trial.Gates pins Q.w.place K gamma alpha} {g' : Trial.Gates pins' Q'.w.place K gamma alpha}
  {f : Equiv.Perm Ω}

def Related (Q Q' : Network u I) (e : Equiv.Perm I) (p R : ℕ) (f : Equiv.Perm Ω)
    (a a' : Ω → Finset I) := ∀ i, Q.Agree Q' e p R i → ∀ x, i ∈ a x ↔ e i ∈ a' (f x)

omit [Fintype I] [Fintype Ω] in
theorem Related.symm {a a' : Ω → Finset I} (h : Q.Related Q' e p R f a a') :
    Q'.Related Q e.symm p R f.symm a' a := fun i hi x => by simpa using (h _ hi.symm (f.symm x)).symm

omit [Fintype I] [Fintype Ω] in
theorem Related.up {a a' : Ω → Finset I} (h : Q.Related Q' e p R f a a') (hle : R ≤ S) :
    Q.Related Q' e p S f a a' := fun i hi => h i (hi.cut hle)

omit [Fintype I] in
theorem left_eq {s : Finset I} (h : ∀ g ∈ s, Q.Agree Q' e p (R+1) g) :
    Q.w.left d s = Q'.w.left d (e.finsetCongr s) := by
  unfold left
  congr 1
  ext z
  constructor
  · rintro ⟨i,hi,hs,he⟩
    exact ⟨e i,by simpa using hi,((h _ hi).shore _).mp hs,((h _ hi).num _).symm.trans he⟩
  · rintro ⟨j,hj,hs,he⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact ⟨i,hi,((h _ hi).shore _).mpr hs,((h _ hi).num _).trans he⟩

namespace Matches

variable (m : Q.Matches Q' e p R r r') (hp : Q.Related Q' e p R f g.pass g'.pass)
  {a b : Budget} {s : Finset I}

include m hp in
theorem cut_map (hab : a ≤ b) (h : Q.Agree Q' e p (R+1+total u b) i)
    (hs : s ∈ g.cuts (r.test area d a i) (r.test area d b i)) :
    e.finsetCongr s ∈ g'.cuts (r'.test area d a (e i)) (r'.test area d b (e i)) ∧
      ∀ j ∈ s, Q.Agree Q' e p (R+1) j := by
  obtain ⟨hk,hc,hm,x,hx⟩ := g.mem_cuts.mp hs
  have cost : total u a ≤ total u b := Finset.sum_le_sum fun x _ => hab x
  have h' := h.cut (show R+1+total u a ≤ _ by omega)
  have hs := m.support (Nat.le_succ _) h' (Round.test_mono _ _ _ _ hab _ hc) hm
  refine ⟨g'.mem_cuts.mpr ⟨by simpa using hk,?_,m.minimal (Nat.le_succ _) h' hm,f x,?_⟩,hs⟩
  · exact (m.covers (Nat.le_succ _) h (fun _ _ => by simp)).mp hc
  intro j hj
  obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
  exact (hp _ ((hs _ hk).cut (Nat.le_succ _)) x).mp (hx hk)

include m hp in
theorem cuts (hab : a ≤ b) (h : Q.Agree Q' e p (R+1+total u b) i) :
    e.finsetCongr.finsetCongr (g.cuts (r.test area d a i) (r.test area d b i)) =
      g'.cuts (r'.test area d a (e i)) (r'.test area d b (e i)) := by
  ext t
  constructor
  · intro hh
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hh
    exact (m.cut_map hp hab h hs).1
  · intro ht
    have hs := (m.symm.cut_map hp.symm hab h.symm ht).1
    rw [e.symm_apply_apply,← Equiv.finsetCongr_symm] at hs
    exact Finset.mem_map.mpr ⟨_,hs,e.finsetCongr.apply_symm_apply t⟩

variable {D : Depths K} {M A : ℝ} {old : Q.w.Round} {old' : Q'.w.Round}
  (L : Ledger g old area d D M A) (L' : Ledger g' old' area d D M A)

def span (u : Dials) (D : Depths K) := 1+size u*D.max

theorem bound (u : Dials) {b : Budget} (hb : b ≤ flat D.max) : 1+total u b ≤ span u D :=
  Nat.add_le_add_left (total_le _ hb) 1

include m hp in
theorem band (h : Q.Agree Q' e p (R+span u D) i) :
    e.finsetCongr.finsetCongr (L.band r i) = L'.band r' (e i) := by
  have hD := D.order
  have hi := h.cut (show R+1 ≤ R+span u D by unfold span; omega)
  have he : L.depth i = L'.depth (e i) := by unfold Ledger.depth ahead; rw [hi.1]
  have hl : flat D.near ≤ L.depth i :=
    (show flat D.near ≤ flat D.band from fun _ => show D.near ≤ D.band by omega).trans (L.range_depth i).1
  have hh := bound u ((L.range_depth i).2.trans (show flat (D.band+1) ≤ flat D.max from fun _ => hD.2.2.2.2))
  unfold Ledger.band Ledger.book
  rw [← he]
  exact m.cuts hp hl (h.cut (by omega))

include hp in
theorem close_map (m : Q.Matches Q' e p R old old') (h : Q.Agree Q' e p (R+span u D) i)
    {z : ℕ} (hs : s ∈ L.close i z) : e.finsetCongr s ∈ L'.close (e i) z := by
  obtain ⟨hs,j,hj,ho,hl,hh⟩ := Finset.mem_filter.mp hs
  have hD := D.order
  have hb : flat (4*D.near) ≤ flat D.max := fun _ => show 4*D.near ≤ D.max by omega
  have h₁ := bound u hb
  have h₂ := Nat.le_mul_of_pos_right (size u) (by omega : 0 < D.max)
  have h' := h.cut (show R+1+size u ≤ R+span u D by unfold span; omega)
  have le : flat D.near ≤ flat (4*D.near) := fun _ => show D.near ≤ 4*D.near by omega
  obtain ⟨hs,hs'⟩ := m.cut_map hp le (h.cut (by omega)) hs
  have eq := (hs' _ hj).num d
  have eq' := (h'.cut (show R+1 ≤ _ by omega)).num d
  have he := left_eq (d := d) hs'
  exact Finset.mem_filter.mpr ⟨hs,e j,by simpa using hj,m.on ho h',by omega,by omega⟩

include hp in
theorem close (m : Q.Matches Q' e p R old old') (h : Q.Agree Q' e p (R+span u D) i) (z : ℕ) :
    e.finsetCongr.finsetCongr (L.close i z) = L'.close (e i) z := by
  ext t
  constructor
  · intro hh
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hh
    exact close_map hp L L' m h hs
  · intro ht
    have hs := close_map hp.symm L' L m.symm h.symm ht
    rw [e.symm_apply_apply,← Equiv.finsetCongr_symm] at hs
    exact Finset.mem_map.mpr ⟨_,hs,e.finsetCongr.apply_symm_apply t⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- Tracks
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I : Type} [Fintype I] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p R k : ℕ} {v : u.Valid} {c : u.History k}

def reach (u : Dials) (k : ℕ) := Matches.span u (u.D k)

def radius (u : Dials) : ℕ → ℕ
  | 0 => 1
  | k+1 => radius u k + reach u k + reach u k + 2 + reach u k + 2

theorem radius_mono (u : Dials) : Monotone (radius u) := by
  apply monotone_nat_of_le_succ
  intro k; rw [radius]; omega

def checkRadius (u : Dials) (k : ℕ) := radius u k + reach u k
def midRadius (u : Dials) (k : ℕ) := checkRadius u k + reach u k + 2

structure Tracks (e : Equiv.Perm I) (p : ℕ) (g : Q.Process v k c) (g' : Q'.Process v k c) : Prop where
  pins : g.raw.pins.Equivariant g'.raw.pins e (u.tables e)
  round : Q.Matches Q' e p (radius u k) g.round g'.round
  pass : Q.Related Q' e p (radius u k) (u.tables e) g.rule.pass g'.rule.pass

namespace Tracks

variable {g : Q.Process v k c} {g' : Q'.Process v k c} (h : Tracks e p g g') {i : I}

include h in
theorem checked : Q.Related Q' e p (checkRadius u k) (u.tables e) g.checked.pass g'.checked.pass := by
  intro i hi x
  have hD := (u.D k).order
  have cost := Matches.bound u (D := u.D k) (show flat (u.D k).step ≤ flat (u.D k).max from
    fun _ => show (u.D k).step ≤ (u.D k).max by have := (u.D k).order; unfold Depths.near at *; omega)
  have hh := hi.cut (show radius u k + 1 + total u (flat (u.D k).step) ≤ checkRadius u k by
    unfold checkRadius reach; omega)
  have eq := (hh.cut (show radius u k + 1 ≤ _ by omega)).place
  let d := u.east k c
  have bad : ∀ x, Stage.bad u k g.rule g.round d i x ↔ Stage.bad u k g'.rule g'.round d (e i) (u.tables e x) := by
    intro x
    simp only [Stage.bad,Stamp.bad,Round.Cover,home,← eq]
    apply h.round.covers (Nat.le_succ _) hh
    intro j hj
    simp only [Coins.Rules.watch,Coins.Raw.force_empty,Finset.mem_sdiff,Stamp.hidden,
      Finset.mem_filter,Finset.mem_univ,true_and,hj.place,eq,h.pass _ (hj.cut (Nat.le_succ _)) x]
  have base := h.pass i (hh.cut (by omega)) x
  have hs := h.pins.screen u.tests bad x
  simp only [Process.checked,Stage.screened,Coins.Rules.mem,Coins.Rules.screen,← and_assoc] at *
  exact and_congr base hs

variable (hk : k < u.h) (s : u.Scale) (b : u.Bin)

include h in
theorem scale (hi : Q.Agree Q' e p (checkRadius u k + reach u k) i) :
    g.stage.scale v hk i = g'.stage.scale v hk (e i) := by
  have eq := (hi.cut (show 1 ≤ _ by unfold reach Matches.span; omega)).place
  let j := Q.w.place i / u.a^(k+1)
  let L := g.stage.ledger v hk j
  let L' := g'.stage.ledger v hk j
  have hr := h.round.up (show radius u k ≤ checkRadius u k by unfold checkRadius; omega)
  have hh : ∀ z, e.finsetCongr.finsetCongr (L.close i z) = L'.close (e i) z :=
    fun z => Matches.close h.checked L L' hr hi z
  have hs : L.colors u.a u.h u.theta i = L'.colors u.a u.h u.theta (e i) := by
    funext t
    simp only [Ledger.colors,h.pins.mass,hh]
  exact hs.trans (congrArg (fun a => (g'.stage.ledger v hk (a/u.a^(k+1))).colors u.a u.h u.theta (e i)) eq)

include h in
theorem mid (hp : 2*k < p) :
    Q.Matches Q' e p (midRadius u k) (g.mid hk s) (g'.mid hk s) := by
  apply h.round.refine (a := u.ticket hk c s none) hp (S := checkRadius u k + reach u k)
  · intro i hi; rw [h.scale hk hi]
  · unfold checkRadius; omega

include h in
theorem band (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) :
    e.finsetCongr.finsetCongr (g.stage.band v hk (g.mid hk s) i) = g'.stage.band v hk (g'.mid hk s) (e i) := by
  have eq := (hi.cut (show 1 ≤ _ by unfold midRadius; omega)).place
  let j := Q.w.place i / u.a^(k+1)
  have h₁ : Q.w.place i ∈ piece (u.a^(k+1)) j := rfl
  have h₂ : Q'.w.place (e i) ∈ piece (u.a^(k+1)) j := eq ▸ h₁
  rw [g.stage.band_eq v hk h₁,g'.stage.band_eq v hk h₂]
  apply (h.mid hk s hp).band (h.checked.up (by unfold midRadius; omega)) _ _ hi

include h in
theorem pick (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) :
    g.stage.pick v hk (g.mid hk s) i = g'.stage.pick v hk (g'.mid hk s) (e i) := by
  unfold Stage.pick
  rw [h.pins.mass,h.band hk s hp hi]

include h in
theorem last (hp : 2*k+1 < p) :
    Q.Matches Q' e p (radius u (k+1)) (g.last hk s b) (g'.last hk s b) := by
  apply (h.mid hk s (by omega)).refine (a := u.ticket hk c s (some b)) hp (S := midRadius u k + reach u k)
  · intro i hi; rw [h.pick hk s (by omega) hi]
  · omega

include h in
theorem bars (hp : 2*k < p) (hi : Q.Agree Q' e p (midRadius u k + reach u k) i) (x : Table (u.Cell I)) :
    Coins.All (g.stage.bars v hk (v.foil hk g.stage.rate) (g.mid hk s) i) x ↔
    Coins.All (g'.stage.bars v hk (v.foil hk g'.stage.rate) (g'.mid hk s) (e i)) (u.tables e x) := by
  unfold Stage.bars
  rw [h.pick hk s hp hi,← h.band hk s hp hi]
  split
  · simp [Coins.All]
  · rename_i j hj
    simp only [Coins.All,Foil.bits,Finset.forall_mem_image,Equiv.finsetCongr_apply,Finset.forall_mem_map]
    apply forall_congr'; intro a
    apply imp_congr_right; intro _
    exact iff_of_eq (congrArg (· = true) (u.tables_apply e x (⟨k+1,by omega⟩,.inr (j,a))).symm)

include h in
theorem succ (hp : 2*k+1 < p) : Tracks e p (g.succ hk s b) (g'.succ hk s b) := by
  have atom := v.atom_same e (⟨k+1,by omega⟩ : Fin (u.h+1))
  refine ⟨⟨(g.succ hk s b).stage.rate.trans (g'.succ hk s b).stage.rate.symm,v.invariant e,?_⟩,
    h.last hk s b hp,?_⟩
  · intro i x
    simp only [Process.succ,Coins.Raw.join_success,Finset.mem_inter]
    exact and_congr (h.pins.success _ _) (atom _ _)
  intro i hi x
  have hh := hi.cut (show midRadius u k + reach u k ≤ radius u (k+1) by
    unfold midRadius checkRadius; rw [radius]; omega)
  have hg := h.checked i (hh.cut (by unfold midRadius; omega)) x
  have hb := h.bars hk s (by omega) hh x
  simp only [Process.succ,Stage.advance,Stamp.Fresh.advance,Coins.Rules.next_pass]
  exact and_congr hg (and_congr (atom i x) hb)

end Tracks
end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- Locality
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I : Type} [Fintype I] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p k : ℕ} (v : u.Valid)

theorem tracks (hk : k ≤ u.h) (hp : 2*k ≤ p) (c : u.History k) :
    Tracks e p (Q.process v k hk c) (Q'.process v k hk c) := by
  induction k with
  | zero =>
    refine ⟨⟨rfl,v.invariant e,v.atom_same e 0⟩,Matches.first,?_⟩
    intro i _ x
    simp only [process,Coins.Rules.mem,Coins.Rules.initial,Coins.All,Finset.notMem_empty,IsEmpty.forall_iff,
      implies_true,and_true]
    exact v.atom_same e 0 _ _
  | succ k ih =>
    obtain ⟨⟨c,s⟩,b⟩ := c
    exact (ih (by omega) (by omega) c).succ (by omega) s b (by omega)

def window (u : Dials) := radius u (u.h+1)

theorem window_pos (u : Dials) : 0 < window u := by unfold window; rw [radius]; omega

theorem local_want (a : u.Ticket) {i : I} (h : Q.Agree Q' e (u.phase a) (window u) i) :
    Q.want v a i ↔ Q'.want v a (e i) := by
  obtain ⟨⟨k,hk⟩,⟨c,s⟩,b⟩ := a
  have hr : radius u (k+1) ≤ window u := radius_mono u (by omega)
  rw [radius] at hr
  cases b with
  | none =>
    have g := tracks (Q := Q) (Q' := Q') (e := e) v hk.le (le_refl (2*k)) c
    have eq := g.scale hk (h.cut (show checkRadius u k+reach u k ≤ window u by unfold checkRadius; omega))
    simp only [want,eq]
  | some b =>
    have g := tracks (Q := Q) (Q' := Q') (e := e) v hk.le (Nat.le_succ (2*k)) c
    have eq := g.pick hk s (by omega) (h.cut (show midRadius u k+reach u k ≤ window u by
      unfold midRadius checkRadius; omega))
    simp only [want,eq]

theorem local_pass (c : u.History u.h) {i : I} (h : Q.Agree Q' e (2*u.h) (window u) i)
    (x : Table (u.Cell I)) : Q.passes v c x i ↔ Q'.passes v c (u.tables e x) (e i) :=
  (tracks v le_rfl le_rfl c).checked _ (h.cut (by unfold window checkRadius; rw [radius]; omega)) x

theorem final_fits (Q : Network u I) (c : u.History u.h) : Q.Fits (2*u.h) (Q.done v c).round :=
  (tracks (Q := Q) (Q' := Q) (e := Equiv.refl I) v le_rfl le_rfl c).round.fits

def Enrolled (u : Dials) : ∀ k, u.History k → u.Ticket → Prop
  | 0,_,_ => False
  | k+1,c,a => Enrolled u k c.1.1 a ∨ ∃ hk : k < u.h,
      a = u.ticket hk c.1.1 c.1.2 none ∨ a = u.ticket hk c.1.1 c.1.2 (some c.2)

theorem color (Q : Network u I) (key : Bool → I) (k : ℕ) (hk : k ≤ u.h) :
    ∃ c : u.History k, ∀ a, Enrolled u k c a → Q.want v a (key (u.side a)) := by
  induction k with
  | zero => exact ⟨(),fun _ h => h.elim⟩
  | succ k ih =>
    obtain ⟨c,hc⟩ := ih (by omega)
    have h : k < u.h := by omega
    let g := Q.process v k h.le c
    let i := key (u.east k c)
    let s := g.stage.scale v h i
    let b := g.stage.pick v h (g.mid h s) i
    refine ⟨((c,s),b),?_⟩
    rintro a (ha | ⟨_,rfl | rfl⟩)
    · exact hc _ ha
    · rfl
    · rfl

def accepts (Q : Network u I) (v : u.Valid) (a : u.Ticket) (i : I) (d : Bool) :=
  if d = u.side a then Q.want v a (Q.w.step i d)
  else Q.w.live (Q.slot a i) ∧ Q.want v a (Q.w.step (Q.slot a i) (u.side a))

theorem marks (Q : Network u I) {i : I} {d : Bool} (hi : Q.w.Middle i) (hl : Q.w.live i)
    (k : ℕ) (hk : k ≤ u.h) (c : u.History k)
    (ha : ∀ a, Enrolled u k c a → Q.accepts v a i d) : (Q.process v k hk c).round.mark i d := by
  induction k with
  | zero => exact ⟨hi,hl⟩
  | succ k ih =>
    have h : k < u.h := by omega
    exact ⟨⟨ih h.le c.1.1 (fun a h => ha a (.inl h)),ha _ (.inr ⟨h,.inl rfl⟩)⟩,
      ha _ (.inr ⟨h,.inr rfl⟩)⟩

end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- Neighborhood
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

abbrev Edges (X L : Type) := X → L → X

namespace Edges

variable {X L A : Type} [Fintype L] (f : Edges X L)

def ball : ℕ → X → Finset X
  | 0,i => {i}
  | k+1,i => insert i (Finset.univ.biUnion fun l => ball k (f i l))

theorem root (k : ℕ) (i : X) : i ∈ f.ball k i := by cases k <;> simp [ball]

theorem sub (k : ℕ) (i : X) (a : L) : f.ball k (f i a) ⊆ f.ball (k+1) i := by
  intro j hj; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,hj⟩)

theorem grow (i : X) {k m : ℕ} (hm : k ≤ m) : f.ball k i ⊆ f.ball m i := by
  induction k generalizing m i with
  | zero => simpa [ball] using f.root m i
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m =>
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact f.root _ _
      · obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hj
        exact f.sub _ _ a (ih _ (by omega) ha)

def bound (L : Type) [Fintype L] (k : ℕ) := (Fintype.card L+1)^k

theorem card (k : ℕ) (i : X) : (f.ball k i).card ≤ bound L k := by
  induction k generalizing i with
  | zero => simp [ball,bound]
  | succ k ih =>
    unfold ball
    apply (Finset.card_insert_le ..).trans
    have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ih (f i a))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
    have hh := Finset.card_biUnion_le.trans h
    have pos : 0 < bound L k := by unfold bound; positivity
    rw [show bound L (k+1) = Fintype.card L*bound L k + bound L k by simp [bound,pow_succ',add_mul]]
    exact Nat.add_le_add hh pos

theorem decreasing (rank : X → ℕ) (hr : ∀ i a, rank (f i a) ≤ rank i) (k : ℕ) (i : X) :
    ∀ j ∈ f.ball k i, rank j ≤ rank i := by
  induction k generalizing i with
  | zero => simp [ball]
  | succ k ih =>
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rfl
    · obtain ⟨a,_,ha⟩ := Finset.mem_biUnion.mp hj
      exact (ih _ _ ha).trans (hr _ a)

def View (L A : Type) : ℕ → Type
  | 0 => A
  | k+1 => View L A k × (L → View L A k)

instance viewFinite [Fintype A] (k : ℕ) : Fintype (View L A k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype A)
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (View L A k × (L → View L A k)))

def view (a : X → A) : ∀ k, X → View L A k
  | 0,i => a i
  | k+1,i => (view a k i,fun l => view a k (f i l))

omit [Fintype L] in
theorem trunc (a : X → A) {k m : ℕ} (h : k ≤ m) {i j : X} (he : f.view a m i = f.view a m j) :
    f.view a k i = f.view a k j := by
  induction m,h using Nat.le_induction with
  | base => exact he
  | succ m _ ih => exact ih (congrArg Prod.fst he)

omit [Fintype L] in
theorem targets (a : X → A) {k : ℕ} {i j : X} (he : f.view a (k+1) i = f.view a (k+1) j) (l : L) :
    f.view a k (f i l) = f.view a k (f j l) := congrFun (congrArg Prod.snd he) l

def tally (a : X → A) (k : ℕ) (i : X) := (f.ball k i).image a

def score (a : X → A) (S : Finset A) (m : ℕ) (i : X) :=
  ∑ k ∈ Finset.range (m+1), ((f.tally a k i) ∩ S).card

theorem score_falls (a : X → A) (S : Finset A) {m : ℕ} (hs : S.card ≤ m) {i : X} {l : L}
    (hi : a i ∈ S) (hn : a i ∉ f.tally a m (f i l)) :
    f.score a S m (f i l) < f.score a S m i := by
  let c := fun i k => ((f.tally a k i) ∩ S).card
  have step : ∀ k ∈ Finset.range m, c (f i l) k + 1 ≤ c i (k+1) := by
    intro k hk
    have sub := Finset.image_mono a (f.sub k i l)
    have notin : a i ∉ f.tally a k (f i l) :=
      fun h => hn (Finset.image_mono a (f.grow _ (Finset.mem_range.mp hk).le) h)
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_inter sub Finset.Subset.rfl,fun he => ?_⟩
    have hh : a i ∈ f.tally a (k+1) i ∩ S :=
      Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (f.root _ _),hi⟩
    exact notin (Finset.mem_inter.mp (he.symm ▸ hh)).1
  have hh := Finset.sum_le_sum step
  have pos : 0 < c i 0 := Finset.card_pos.mpr
    ⟨a i,Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (f.root _ _),hi⟩⟩
  have last : c (f i l) m ≤ m := (Finset.card_le_card Finset.inter_subset_right).trans hs
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,mul_one] at hh
  change (∑ k ∈ Finset.range (m+1), c (f i l) k) < ∑ k ∈ Finset.range (m+1), c i k
  rw [Finset.sum_range_succ,Finset.sum_range_succ']
  omega

end Edges
end OAI.Geometry.Hirsch.Layer
end

-- Realization
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

abbrev Action (u : Dials) := Bool ⊕ u.Ticket

variable {X I : Type} {u : Dials} (Q : Network u X) (p : ℕ)

def edges : Edges X (Action u) := fun i a =>
  match a with
  | .inl d => if Q.w.live i then Q.w.step i d else i
  | .inr a => if u.phase a < p then Q.slot a i else i

def ball := (Q.edges p).ball

variable {Q p} {i : X} {R : ℕ}

theorem basic_sub (hl : Q.w.live i) (d : Bool) : Q.ball p R (Q.w.step i d) ⊆ Q.ball p (R+1) i := by
  simpa [ball,edges,hl] using (Q.edges p).sub R i (.inl d)

theorem slot_sub {a : u.Ticket} (ha : u.phase a < p) : Q.ball p R (Q.slot a i) ⊆ Q.ball p (R+1) i := by
  simpa [ball,edges,ha] using (Q.edges p).sub R i (.inr a)

theorem Agree.compare {Q₁ Q₂ : Network u I} {f g : X → I} {e : Equiv.Perm I}
    (h₁ : Q.Agree Q₁ f p R i) (h₂ : Q.Agree Q₂ g p R i)
    (he : ∀ j ∈ Q.ball p R i, e (f j) = g j) : Q₁.Agree Q₂ e p R (f i) := by
  induction R generalizing i with
  | zero => exact True.intro
  | succ R ih =>
    have eq := he i ((Q.edges p).root _ i)
    simp only [Agree,eq]
    refine ⟨h₁.1.symm.trans h₂.1,h₁.2.1.symm.trans h₂.2.1,?_,?_⟩
    · intro d hl
      have hl' := h₁.2.1.mpr hl
      obtain ⟨e₁,a₁⟩ := h₁.2.2.1 d hl'
      obtain ⟨e₂,a₂⟩ := h₂.2.2.1 d hl'
      rw [← e₁,← e₂]
      have hh := fun j hj => he j (basic_sub hl' d hj)
      exact ⟨hh _ ((Q.edges p).root _ _),ih a₁ a₂ hh⟩
    · intro a ha
      obtain ⟨e₁,a₁⟩ := h₁.2.2.2 a ha
      obtain ⟨e₂,a₂⟩ := h₂.2.2.2 a ha
      rw [← e₁,← e₂]
      have hh := fun j hj => he j (slot_sub ha hj)
      exact ⟨hh _ ((Q.edges p).root _ _),ih a₁ a₂ hh⟩

theorem permute (A : Finset X) (f g : X → I)
    (he : ∀ i ∈ A, ∀ j ∈ A, f i = f j ↔ g i = g j) :
    ∃ e : Equiv.Perm I, ∀ i ∈ A, e (f i) = g i := by
  let S := A.image f
  have ex : ∀ y : ↥S, ∃ i ∈ A, f i = y.val := fun y => Finset.mem_image.mp y.property
  choose rep hr hf using ex
  have inj : Function.Injective (fun y => g (rep y)) := fun x y h =>
    Subtype.ext ((hf x).symm.trans (((he _ (hr x) _ (hr y)).mpr h).trans (hf y)))
  obtain ⟨e,hh⟩ := Equiv.Perm.exists_extending_pair (fun y : ↥S => y.val) _ Subtype.val_injective inj
  refine ⟨e,fun i hi => ?_⟩
  let y : ↥S := ⟨f i,Finset.mem_image_of_mem _ hi⟩
  exact (hh y).trans ((he _ (hr y) _ hi).mp (hf y))

structure Consistent (Q : Network u X) (p : ℕ) (A : Finset X) (f : X → I) (rank : X → ℕ) : Prop where
  layer : ∀ i j, f i = f j → Q.w.layer i = Q.w.layer j
  live : ∀ i j, f i = f j → (Q.w.live i ↔ Q.w.live j)
  height : ∀ i j, f i = f j → rank i = rank j
  next : ∀ i ∈ A, ∀ j ∈ A, f i = f j → ∀ a, f (Q.edges p i a) = f (Q.edges p j a)
  falls : ∀ i ∈ A, ∀ a, Q.edges p i a ≠ i → rank (Q.edges p i a) < rank i

theorem Consistent.realize {A : Finset X} {f : X → I} {rank : X → ℕ} (h : Q.Consistent p A f rank)
    (x : X) : ∃ N : Network u I, ∀ R i, Q.ball p R i ⊆ A → Q.Agree N f p R i := by
  let B := A.image f
  have choose : ∀ b, ∃ i, (b ∈ B → i ∈ A) ∧ (b ∈ Set.range f → f i = b) := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hb
      exact ⟨i,fun _ => hi,fun _ => he⟩
    by_cases hh : b ∈ Set.range f
    · exact ⟨hh.choose,fun h => (hb h).elim,fun _ => hh.choose_spec⟩
    · exact ⟨x,fun h => (hb h).elim,fun h => (hh h).elim⟩
  choose rep mem eq using choose
  have key : ∀ i, f (rep (f i)) = f i := fun i => eq _ ⟨i,rfl⟩
  have layer := fun i => h.layer _ _ (key i)
  have ht := fun i => h.height _ _ (key i)
  let board : Board I (u.a^u.h) := {
    layer := fun b => Q.w.layer (rep b)
    bound := fun b => Q.w.bound _
    live := fun b => b ∈ B ∧ Q.w.live (rep b)
    step := fun b d => f (Q.w.step (rep b) d)
    west := fun b hb => by rw [layer]; exact Q.w.west _ hb.2
    east := fun b hb => by rw [layer]; exact Q.w.east _ hb.2
    rank := fun b => rank (rep b)
    decrease := by
      intro b hb d; rw [ht]
      have hh := h.falls _ (mem _ hb.1) (.inl d)
      simp only [edges,if_pos hb.2] at hh
      exact hh (fun he => (Q.w.decrease _ hb.2 d).ne (congrArg Q.w.rank he)) }
  let N : Network u I := {
    w := board
    slot := fun a b => if b ∈ B ∧ u.phase a < p then f (Q.slot a (rep b)) else b
    same := fun a b => by split <;> simp [board,layer,Q.same]
    jump := by
      intro a b hn
      split at hn
      · rename_i hh
        have ne : Q.slot a (rep b) ≠ rep b := by
          intro he; apply hn; rw [he,eq b (by obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hh.1; exact ⟨i,hi⟩)]
        have hd := h.falls _ (mem _ hh.1) (.inr a)
        simp only [edges,if_pos hh.2] at hd
        simp only [if_pos hh,board,ht]
        exact ⟨⟨hh.1,(Q.jump _ _ ne).1⟩,hd ne⟩
      · contradiction }
  refine ⟨N,fun R => ?_⟩
  induction R with
  | zero => exact fun _ _ => True.intro
  | succ R ih =>
    intro i hi
    have hm := hi ((Q.edges p).root _ i)
    have hb : f i ∈ B := Finset.mem_image_of_mem _ hm
    have live := h.live _ _ (key i)
    have next := h.next i hm _ (mem _ hb) (key i).symm
    refine ⟨(layer i).symm,by simp [N,board,hb,live],?_,?_⟩
    · intro d hl
      exact ⟨by simpa [N,board,edges,hl,live.mpr hl] using next (.inl d),ih _ ((basic_sub hl d).trans hi)⟩
    · intro a ha
      exact ⟨by simpa [N,edges,hb,ha] using next (.inr a),ih _ ((slot_sub ha).trans hi)⟩

end OAI.Geometry.Hirsch.Layer.Board.Network
end

-- Names
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

namespace Naming

variable (u : Dials)

def P := 2*u.h
def R := Network.window u + 2 + Network.size u * (u.D u.h).step
def M := 2*Edges.bound (Network.Action u) (R u)
def H := 2*(P u+1)*(M u)^2+1
def N := H u^(P u+1)

theorem Hpos : 0 < H u := Nat.zero_lt_succ _
theorem Npos : 0 < N u := pow_pos (Hpos u) _

abbrev Radii := Fin (N u)
abbrev Label := Bool ⊕ (u.Ticket × Radii u)
abbrev Symbol := Fin (Edges.bound (Label u) (M u+1)+1)
abbrev NodeData := Fin (Network.size u) × Bool × (Fin (M u+1) → Finset (Symbol u))
def NodeName := Σ r : Radii u, Edges.View (Label u) (NodeData u) r.val

instance : Fintype (NodeName u) := inferInstanceAs (Fintype (Σ r : Radii u, Edges.View (Label u) (NodeData u) r.val))

def length (p : ℕ) := H u^(P u-p)
def block (p r : ℕ) := r / length u p

theorem length_pos (p : ℕ) : 0 < length u p := pow_pos (Hpos u) _

theorem ancestor {p q r s : ℕ} (hq : q < p) (hp : p ≤ P u)
    (h : block u p r / H u = block u p s / H u) : block u q r = block u q s := by
  have he : length u q = (length u p * H u)*H u^(p-q-1) := by
    unfold length; rw [← pow_succ,← pow_add]; congr 1; omega
  simp only [block,he,← Nat.div_div_eq_div_mul]
  exact congrArg (· / _) h

end Naming

open Naming

structure Legs (u : Dials) (X : Type) where
  w : Board X (u.a^u.h)
  along : X → Bool → X → Prop
  info : ∀ i d j, along i d j → w.Middle i ∧ w.live i ∧ w.live j ∧
    w.layer j = w.layer i ∧ w.step j d = w.step i d ∧ (j = i ∨ w.rank j < w.rank i)

namespace Legs

variable {u : Dials} {X : Type} (L : Legs u X)

structure Node (i : X) where
  slot : u.Ticket → Radii u → X
  valid : ∀ a r, slot a r = i ∨ L.along i (!(u.side a)) (slot a r)
  symbol : Symbol u

def empty (i : X) : L.Node i := ⟨fun _ _ => i,fun _ _ => .inl rfl,0⟩

abbrev Decoration := ∀ i, L.Node i

namespace Decoration

variable {L} (A : L.Decoration)

def active (r : Radii u) : Network u X where
  w := L.w
  slot a i := (A i).slot a r
  same a i := ((A i).valid a r).elim (congrArg L.w.layer) (fun h => (L.info _ _ _ h).2.2.2.1)
  jump a i hn := by
    have hh := L.info _ _ _ (((A i).valid a r).resolve_left hn)
    exact ⟨hh.2.1,hh.2.2.2.2.2.resolve_left hn⟩

def fan : Edges X (Label u) := fun i a => match a with
  | .inl d => if L.w.live i then L.w.step i d else i
  | .inr (t,r) => (A i).slot t r

theorem fall (i : X) (a : Label u) (hn : A.fan i a ≠ i) : L.w.rank (A.fan i a) < L.w.rank i := by
  rcases a with d | ⟨t,r⟩
  · by_cases hl : L.w.live i
    · simpa [fan,hl] using L.w.decrease i hl d
    · simp [fan,hl] at hn
  · exact ((A.active r).jump t i hn).2

theorem decrease (i : X) (a : Label u) : L.w.rank (A.fan i a) ≤ L.w.rank i := by
  by_cases he : A.fan i a = i
  · rw [he]
  · exact (A.fall i a he).le

def symbol (i : X) := (A i).symbol

def data (i : X) : NodeData u := (⟨L.w.layer i,L.w.bound i⟩,decide (L.w.live i),
  fun k => A.fan.tally A.symbol k i)

def name (r : Radii u) (i : X) : NodeName u := ⟨r,A.fan.view A.data r i⟩

theorem names (r : Radii u) (i j : X) :
    A.name r i = A.name r j ↔ A.fan.view A.data r.val i = A.fan.view A.data r.val j := by simp [name,NodeName]

def Safe := ∀ i j, j ∈ A.fan.ball (M u+1) i → L.w.rank j < L.w.rank i → A.symbol i ≠ A.symbol j

def Fixed := ∀ i a (r s : Radii u), block u (u.phase a) r.val = block u (u.phase a) s.val → (A i).slot a r = (A i).slot a s

def Break (r : ℕ) (i j : X) := A.fan.view A.data r i = A.fan.view A.data r j ∧
  A.fan.view A.data (r+1) i ≠ A.fan.view A.data (r+1) j

theorem unique_break {i j : X} {r s : ℕ} (hr : A.Break r i j) (hs : A.Break s i j) : r = s := by
  rcases lt_trichotomy r s with hh | hh | hh
  · exact (hr.2 (A.fan.trunc A.data hh hs.1)).elim
  · exact hh
  · exact (hs.2 (A.fan.trunc A.data hh hr.1)).elim

theorem model (safe : A.Safe) (r : Radii u) (p : ℕ) (B : Finset X) (hb : B.card ≤ M u)
    (good : ∀ i ∈ B, ∀ j ∈ B, ¬A.Break r i j) (x : X) :
    ∃ Q : Network u (NodeName u), ∀ k i, (A.active r).ball p k i ⊆ B → (A.active r).Agree Q (A.name r) p k i := by
  let _ : DecidableEq (Symbol u) := fun _ _ => propDecidable _
  let S := B.image A.symbol
  have bound : S.card ≤ M u := Finset.card_image_le.trans hb
  have data : ∀ i j, A.name r i = A.name r j → A.data i = A.data j :=
    fun i j h => A.fan.trunc A.data (Nat.zero_le _) ((A.names _ _ _).mp h)
  apply Network.Consistent.realize (rank := A.fan.score A.symbol S (M u)) _ x
  refine ⟨fun i j h => congrArg (fun a : NodeData u => a.1.val) (data i j h),?_,?_,?_,?_⟩
  · intro i j h
    exact decide_eq_decide.mp (congrArg (fun a : NodeData u => a.2.1) (data i j h))
  · intro i j h
    apply Finset.sum_congr rfl
    intro k hk
    have hh := congrArg (fun a : NodeData u => a.2.2 ⟨k,Finset.mem_range.mp hk⟩) (data i j h)
    exact congrArg (fun s => (s ∩ S).card) hh
  · intro i hi j hj h a
    have eq : A.fan.view A.data (r.val+1) i = A.fan.view A.data (r.val+1) j :=
      by_contra fun hn => good i hi j hj ⟨(A.names _ _ _).mp h,hn⟩
    have each : ∀ a, A.name r (A.fan i a) = A.name r (A.fan j a) :=
      fun a => (A.names _ _ _).mpr (A.fan.targets _ eq a)
    rcases a with d | a
    · exact each (.inl d)
    · by_cases ha : u.phase a < p
      · simpa [Network.edges,ha,active,fan] using each (.inr (a,r))
      · simpa [Network.edges,ha] using h
  intro i hi a hn
  have ex : ∃ b, (A.active r).edges p i a = A.fan i b := by
    rcases a with d | a
    · exact ⟨.inl d,rfl⟩
    · by_cases ha : u.phase a < p
      · exact ⟨.inr (a,r),by simp [Network.edges,ha,active,fan]⟩
      · simp [Network.edges,ha] at hn
  obtain ⟨b,he⟩ := ex
  rw [he] at hn ⊢
  apply A.fan.score_falls A.symbol S bound (Finset.mem_image_of_mem _ hi)
  intro hh
  obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh
  exact safe i j (A.fan.sub _ _ _ hj) ((A.fan.decreasing _ A.decrease _ _ j hj).trans_lt (A.fall _ _ hn)) he.symm

end Decoration
end Legs
end OAI.Geometry.Hirsch.Layer.Board
end

-- Decoration
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

theorem choose_by_rank {X : Type} {Y : X → Type} (rank : X → ℕ) (init : ∀ i, Y i)
    (prop : (∀ i, Y i) → X → Prop)
    (step : ∀ i (a : ∀ i, Y i), ∃ y : Y i, ∀ b, (∀ j, rank j < rank i → a j = b j) → b i = y → prop b i) :
    ∃ b, ∀ i, prop b i := by
  choose take ht using step
  let F := fun i (a : ∀ j, rank j < rank i → Y j) => take i (fun j => if h : rank j < rank i then a j h else init j)
  let wf : WellFounded (fun j i => rank j < rank i) := (measure rank).wf
  let b := wf.fix F
  refine ⟨b,fun i => ht i (fun j => if rank j < rank i then b j else init j) b (by intros; simp_all) ?_⟩
  exact wf.fix_eq F i

namespace Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid)

def Earn (a : u.Ticket) (bin : ℕ) (g : X) :=
  ∀ s : Radii u, block u (u.phase a) s = bin → ∀ Q : Network u (NodeName u),
    (A.active s).Agree Q (A.name s) (u.phase a) (Network.window u) g → Q.want v a (A.name s g)

def Promised (i : X) := ∀ a (r : Radii u) j, L.along i (!(u.side a)) j →
  A.Earn v a (block u (u.phase a) r) (L.w.step j (u.side a)) →
  L.w.live ((A i).slot a r) ∧ A.Earn v a (block u (u.phase a) r) (L.w.step ((A i).slot a r) (u.side a))

def Below (A B : L.Decoration) (k : ℕ) := ∀ i, L.w.rank i < k → A i = B i

variable {A} {B : L.Decoration} {k : ℕ} {i : X}

theorem ball_eq {P : X → Prop} (hc : ∀ i, P i → ∀ a, P (A.fan i a))
    (he : ∀ i, P i → ∀ a, A.fan i a = B.fan i a) (n : ℕ) (hi : P i) :
    A.fan.ball n i = B.fan.ball n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [Edges.ball]
    congr 2
    funext a; rw [← he _ hi a]; exact ih (hc _ hi _)

theorem fan_eq (h : (A i).slot = (B i).slot) (a : Label u) : A.fan i a = B.fan i a := by
  rcases a with d | ⟨t,r⟩
  · rfl
  · simp only [fan,h]

namespace Below

variable (h : A.Below B k) (hi : L.w.rank i < k)
include h hi

theorem data : A.data i = B.data i := by
  unfold Decoration.data
  congr 2
  funext n
  have eq := ball_eq (P := fun j => L.w.rank j < k) (fun j hj a => (A.decrease j a).trans_lt hj)
    (fun j hj => fan_eq (congrArg Node.slot (h _ hj))) n.val hi
  unfold Edges.tally
  rw [← eq]
  let _ : DecidableEq (Symbol u) := fun _ _ => propDecidable _
  apply Finset.image_congr
  intro j hj
  exact congrArg Node.symbol (h _ ((A.fan.decreasing _ A.decrease _ _ _ hj).trans_lt hi))

theorem view (n : ℕ) : A.fan.view A.data n i = B.fan.view B.data n i := by
  induction n generalizing i with
  | zero => exact h.data hi
  | succ n ih =>
    simp only [Edges.view,ih hi]
    congr 1
    funext a
    rw [← fan_eq (congrArg Node.slot (h _ hi)) a]
    exact ih ((A.decrease _ _).trans_lt hi)

theorem name (r : Radii u) : A.name r i = B.name r i := congrArg (Sigma.mk r) (h.view hi r.val)

theorem agree (r : Radii u) (Q : Network u (NodeName u)) (p n : ℕ) :
    (A.active r).Agree Q (A.name r) p n i ↔ (B.active r).Agree Q (B.name r) p n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have eq := h.name hi r
    have step : ∀ d, L.w.live i → L.w.rank (L.w.step i d) < k := fun d hl => (L.w.decrease i hl d).trans hi
    have slot : ∀ t, L.w.rank ((A i).slot t r) < k := fun t => (A.decrease i (.inr (t,r))).trans_lt hi
    have basic : ∀ d, L.w.live i →
        (A.name r (L.w.step i d) = Q.w.step (A.name r i) d ∧ (A.active r).Agree Q (A.name r) p n (L.w.step i d) ↔
         B.name r (L.w.step i d) = Q.w.step (B.name r i) d ∧ (B.active r).Agree Q (B.name r) p n (L.w.step i d)) :=
      fun d hl => by rw [h.name (step d hl),eq,ih (step d hl)]
    have jump : ∀ t, (A.name r ((A i).slot t r) = Q.slot t (A.name r i) ∧
        (A.active r).Agree Q (A.name r) p n ((A i).slot t r) ↔
        B.name r ((B i).slot t r) = Q.slot t (B.name r i) ∧ (B.active r).Agree Q (B.name r) p n ((B i).slot t r)) :=
      fun t => by rw [← h _ hi,h.name (slot t),eq,ih (slot t)]
    constructor
    · exact fun hh => ⟨eq ▸ hh.1,eq ▸ hh.2.1,fun d hl => (basic d hl).mp (hh.2.2.1 d hl),
        fun t ht => (jump t).mp (hh.2.2.2 t ht)⟩
    · exact fun hh => ⟨eq.symm ▸ hh.1,eq.symm ▸ hh.2.1,fun d hl => (basic d hl).mpr (hh.2.2.1 d hl),
        fun t ht => (jump t).mpr (hh.2.2.2 t ht)⟩

theorem earn (a : u.Ticket) (bin : ℕ) : A.Earn v a bin i ↔ B.Earn v a bin i := by
  simp only [Earn,h.agree hi,h.name hi]

end Below

variable (A)

def candidate (i : X) (a : u.Ticket) (bin : ℕ) (j : X) :=
  L.along i (!(u.side a)) j ∧ A.Earn v a bin (L.w.step j (u.side a))

def pick (i : X) (a : u.Ticket) (bin : ℕ) := if h : ∃ j, A.candidate v i a bin j then h.choose else i

def plan (i : X) (sym : Symbol u) : L.Node i where
  slot a r := A.pick v i a (block u (u.phase a) r)
  valid a r := by
    unfold pick; split
    · rename_i h; exact .inr h.choose_spec.1
    · exact .inl rfl
  symbol := sym

theorem promised (h : A.Below B (L.w.rank i)) (sym : Symbol u) (hi : B i = A.plan v i sym) :
    B.Promised v i := by
  intro a r j hj he
  let bin := block u (u.phase a) r
  have low : ∀ j, L.along i (!(u.side a)) j → L.w.rank (L.w.step j (u.side a)) < L.w.rank i := by
    intro j hj
    obtain ⟨_,_,hl,_,_,he⟩ := L.info _ _ _ hj
    exact (L.w.decrease _ hl _).trans_le (he.elim (fun h => by rw [h]) LT.lt.le)
  have ex : ∃ j, A.candidate v i a bin j := ⟨j,hj,(h.earn v (low _ hj) a bin).mpr he⟩
  have eq : (B i).slot a r = ex.choose := by rw [hi]; exact dif_pos ex
  obtain ⟨hj,he⟩ := ex.choose_spec
  rw [eq]
  exact ⟨(L.info _ _ _ hj).2.2.1,(h.earn v (low _ hj) a bin).mp he⟩

theorem exists_decoration (L : Legs u X) (v : u.Valid) :
    ∃ A : L.Decoration, A.Safe ∧ A.Fixed ∧ ∀ i, A.Promised v i := by
  let goal := fun (B : L.Decoration) i =>
    (∀ j ∈ B.fan.ball (M u+1) i, L.w.rank j < L.w.rank i → B.symbol i ≠ B.symbol j) ∧
    (∀ a (r s : Radii u), block u (u.phase a) r = block u (u.phase a) s → (B i).slot a r = (B i).slot a s) ∧
    B.Promised v i
  suffices ∃ B, ∀ i, goal B i by
    obtain ⟨B,hB⟩ := this
    exact ⟨B,fun i => (hB i).1,fun i => (hB i).2.1,fun i => (hB i).2.2⟩
  apply choose_by_rank L.w.rank L.empty
  intro i A
  let trial : L.Decoration := Function.update A i (plan A v i 0)
  let used := (trial.fan.ball (M u+1) i).image trial.symbol
  have size : used.card < Fintype.card (Symbol u) := by
    rw [Fintype.card_fin]
    exact Nat.lt_succ_of_le (Finset.card_image_le.trans (trial.fan.card _ _))
  obtain ⟨sym,hs⟩ : ∃ sym, sym ∉ used := by
    by_contra! hh
    exact size.not_ge (Finset.card_le_card (show Finset.univ ⊆ used from fun x _ => hh x))
  refine ⟨plan A v i sym,fun B h hi => ⟨?_,?_,promised A v h sym hi⟩⟩
  · intro j hj hr he
    have lower : ∀ j, L.w.rank j < L.w.rank i → B j = trial j := by
      intro j hh
      have hn : j ≠ i := fun he => hh.ne (congrArg L.w.rank he)
      simp [trial,hn,h _ hh]
    let near := fun j => j = i ∨ L.w.rank j < L.w.rank i
    have closed : ∀ j, near j → ∀ a, near (fan B j a) := by
      rintro j (rfl | hj) a
      · by_cases he : fan B j a = j
        · exact .inl he
        · exact .inr (fall B _ _ he)
      · exact .inr ((decrease B _ _).trans_lt hj)
    have same : ∀ j, near j → ∀ a, fan B j a = trial.fan j a := by
      intro j hj
      apply fan_eq
      rcases hj with rfl | hj
      · simp [hi,trial,plan]
      · rw [lower _ hj]
    rw [ball_eq closed same _ (.inl rfl)] at hj
    apply hs
    have eq : trial.symbol j = sym := by simpa [symbol,hi,plan,lower _ hr] using he.symm
    exact Finset.mem_image.mpr ⟨j,hj,eq⟩
  · intro a r s he; simp [hi,plan,he]

end Legs.Decoration
end OAI.Geometry.Hirsch.Layer.Board
end

-- Bins
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board

open Naming

namespace Naming

variable (u : Dials) (p : ℕ)

theorem product (hp : p ≤ Naming.P u) : H u ^ p * (length u p * H u) = N u := by
  unfold length N; rw [← pow_succ,← pow_add]; congr 1; omega

theorem parent_lt (hp : p ≤ Naming.P u) (r : Radii u) : block u p r/H u < H u ^ p := by
  unfold block
  rw [Nat.div_div_eq_div_mul,Nat.div_lt_iff_lt_mul (Nat.mul_pos (length_pos ..) (Hpos _)),product _ _ hp]
  exact r.isLt

theorem card_block (j : ℕ) :
    (Finset.univ.filter (fun r : Radii u => block u p r = j)).card ≤ length u p := by
  rw [← Finset.card_range (length u p)]
  apply Finset.card_le_card_of_injOn (fun r => r.val % length u p)
  · exact fun r _ => Finset.mem_range.mpr (Nat.mod_lt _ (length_pos ..))
  · intro r hr s hs he
    have eq := (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hs).2.symm
    change r.val / length u p = s.val / length u p at eq
    exact Fin.ext ((Nat.mod_add_div ..).symm.trans ((congrArg₂ (· + ·) he (congrArg (length u p * ·) eq)).trans
      (Nat.mod_add_div ..)))

end Naming

namespace Legs.Decoration

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (key : Bool → X) (p : ℕ)

def region (r : Radii u) := (A.active r).ball p (R u) (key false) ∪ (A.active r).ball p (R u) (key true)

theorem region_bound (r : Radii u) : (A.region key p r).card ≤ M u := by
  have h := ((A.active r).edges p).card (R u) (key false)
  have h' := ((A.active r).edges p).card (R u) (key true)
  unfold region M Network.ball
  exact (Finset.card_union_le ..).trans ((Nat.add_le_add h h').trans_eq (two_mul _).symm)

theorem region_sub (r : Radii u) (d : Bool) : (A.active r).ball p (R u) (key d) ⊆ A.region key p r := by
  cases d
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

def Calm (r : Radii u) := ∀ i ∈ A.region key p r, ∀ j ∈ A.region key p r, ∀ m,
  block u p m = block u p r → ¬A.Break m i j

variable {A key p} {r s : Radii u}

theorem Fixed.slots (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u)
    {a : u.Ticket} (ha : u.phase a < p) (i : X) : (A.active r).slot a i = (A.active s).slot a i :=
  h i a r s (ancestor _ ha hp he)

theorem Fixed.region (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u) :
    A.region key p r = A.region key p s := by
  have eq : (A.active r).edges p = (A.active s).edges p := by
    funext i a
    rcases a with d | a
    · rfl
    · by_cases ha : u.phase a < p
      · simp only [Network.edges,if_pos ha,h.slots hp he ha]
      · simp [Network.edges,ha]
  unfold Decoration.region Network.ball; rw [eq]

theorem Fixed.agree (h : A.Fixed) (hp : p ≤ Naming.P u) (he : block u p r/H u = block u p s/H u)
    {I : Type} {Q : Network u I} {f : X → I} {k : ℕ} {i : X}
    (hh : (A.active r).Agree Q f p k i) : (A.active s).Agree Q f p k i := by
  induction k generalizing i with
  | zero => exact True.intro
  | succ k ih =>
    refine ⟨hh.1,hh.2.1,fun d hl => ⟨(hh.2.2.1 d hl).1,ih (hh.2.2.1 d hl).2⟩,?_⟩
    intro a ha
    rw [← h.slots hp he ha]
    exact ⟨(hh.2.2.2 a ha).1,ih (hh.2.2.2 a ha).2⟩

theorem Calm.permute (h : A.Calm key p r) (he : block u p s = block u p r) :
    ∃ e : Equiv.Perm (NodeName u), ∀ i ∈ A.region key p r, e (A.name r i) = A.name s i := by
  apply Network.permute
  intro i hi j hj
  rw [A.names,A.names]
  let eq := fun k => A.fan.view A.data k i = A.fan.view A.data k j
  have aux : ∀ x y : ℕ, x ≤ y → block u p x = block u p r → block u p y = block u p r → (eq x ↔ eq y) := by
    intro x y hxy hx
    induction y,hxy using Nat.le_induction with
    | base => exact fun _ => Iff.rfl
    | succ y hle ih =>
      intro hy
      have h₁ : block u p x ≤ block u p y := Nat.div_le_div_right hle
      have h₂ : block u p y ≤ block u p (y+1) := Nat.div_le_div_right (Nat.le_succ y)
      have mid : block u p y = block u p r := by omega
      exact (ih mid).trans ⟨fun hh => by_contra (fun hn => h i hi j hj y mid ⟨hh,hn⟩),
        fun hh => A.fan.trunc _ (Nat.le_succ _) hh⟩
  rcases le_total r.val s.val with hr | hr
  · exact aux _ _ hr rfl he
  · exact (aux _ _ hr he rfl).symm

def Good (A : L.Decoration) (key : Bool → X) (r : Radii u) := ∀ p ≤ Naming.P u, A.Calm key p r

theorem Good.model (h : A.Good key r) (hs : A.Safe) :
    ∃ Q : Network u (NodeName u), ∀ d, (A.active r).Agree Q (A.name r) (Naming.P u) (R u) (key d) := by
  obtain ⟨Q,hQ⟩ := A.model hs r (Naming.P u) _ (A.region_bound key _ r)
    (fun i hi j hj => h _ le_rfl i hi j hj _ rfl) (key true)
  exact ⟨Q,fun d => hQ _ _ (A.region_sub key _ r d)⟩

theorem Good.earn (h : A.Good key r) (fixed : A.Fixed) (v : u.Valid) (a : u.Ticket) (d : Bool)
    {Q : Network u (NodeName u)} (hq : (A.active r).Agree Q (A.name r) (Naming.P u) (R u) (key d))
    (hw : Q.want v a (A.name r (key d))) : A.Earn v a (block u (u.phase a) r) (key d) := by
  intro s he Q' hq'
  have hp : u.phase a ≤ Naming.P u := (u.phase_lt _).le
  have hr : Network.window u ≤ R u := by unfold R; omega
  obtain ⟨e,he'⟩ := (h _ hp).permute he
  have hh := fixed.agree hp (congrArg (· / H u) he) hq'
  have agree := (hq.less hp hr).compare hh (fun i hi =>
    he' i (A.region_sub key _ r d (((A.active r).edges _).grow _ hr hi)))
  have eq := he' (key d) (A.region_sub key _ r d (((A.active r).edges _).root _ _))
  exact eq ▸ (Network.local_want v a agree).mp hw

end Legs.Decoration
end OAI.Geometry.Hirsch.Layer.Board
end

-- Frequency
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (key : Bool → X) (p : ℕ)

def failures := Finset.univ.filter fun r => ¬A.Calm key p r

theorem few (fixed : A.Fixed) (hp : p ≤ Naming.P u) :
    (A.failures key p).card * H u ≤ M u ^ 2 * N u := by
  let fail := fun j => (A.failures key p).filter fun r => block u p r.val / H u = j
  have each : ∀ j, (fail j).card ≤ M u^2 * length u p := by
    intro j
    by_cases hem : (fail j).Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp hem]
    obtain ⟨r,hr⟩ := hem
    have eq := (Finset.mem_filter.mp hr).2
    let S := A.region key p r
    let idx := fun t : X × X => sInf {m | A.Break m t.1 t.2}
    let cover := fun t => Finset.univ.filter fun s : Radii u => block u p s = block u p (idx t)
    have sub : fail j ⊆ (S ×ˢ S).biUnion cover := by
      intro s hs
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
      have hh := (Finset.mem_filter.mp hs).2
      unfold Calm at hh
      rw [fixed.region hp (he.trans eq.symm)] at hh
      push Not at hh
      obtain ⟨x,hx,y,hy,m,hm,hbreak⟩ := hh
      have hid : idx (x,y) = m := A.unique_break (Nat.sInf_mem (s := {m | A.Break m x y}) ⟨m,hbreak⟩) hbreak
      exact Finset.mem_biUnion.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hid,hm]⟩⟩
    have bound := Finset.card_biUnion_le_card_mul (S ×ˢ S) cover _ (fun t _ => card_block u p _)
    refine ((Finset.card_le_card sub).trans bound).trans ?_
    rw [Finset.card_product,pow_two]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (A.region_bound key p r) (A.region_bound key p r))
  let parents := Finset.range (H u ^ p)
  have sub : A.failures key p ⊆ parents.biUnion fail := fun r hr =>
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_range.mpr (parent_lt u p hp r),Finset.mem_filter.mpr ⟨hr,rfl⟩⟩
  have high := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul parents fail _ (fun j _ => each j))
  calc
    _ ≤ parents.card * (M u^2 * length u p) * H u := Nat.mul_le_mul_right _ high
    _ = _ := by rw [← product u p hp]; simp only [parents,Finset.card_range]; ring

theorem frequent (fixed : A.Fixed) :
    N u ≤ 2*(Finset.univ.filter (A.Good key)).card := by
  let bad := Finset.univ.filter fun r => ¬A.Good key r
  let stages := Finset.range (Naming.P u+1)
  have incl : bad ⊆ stages.biUnion (A.failures key) := by
    intro r hr
    have h := (Finset.mem_filter.mp hr).2
    unfold Good at h; push Not at h
    obtain ⟨p,hp,hn⟩ := h
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  have high : bad.card * H u ≤ (Naming.P u+1)*(M u^2*N u) := by
    calc
      _ ≤ (∑ p ∈ stages, (A.failures key p).card)*H u :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card incl).trans Finset.card_biUnion_le)
      _ ≤ ∑ _ ∈ stages, M u^2*N u := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun p hp => A.few key p fixed (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
      _ = _ := by simp [stages]
  have small : 2*bad.card ≤ N u := by
    apply Nat.le_of_mul_le_mul_right _ (Hpos u)
    calc
      _ = 2*(bad.card*H u) := by ring
      _ ≤ 2*((Naming.P u+1)*(M u^2*N u)) := Nat.mul_le_mul_left _ high
      _ ≤ _ := by unfold H; nlinarith
  have split := Finset.card_filter_add_card_filter_not (s := Finset.univ) (A.Good key)
  simp only [Finset.card_univ,Fintype.card_fin] at split
  change _ + bad.card = N u at split
  omega

end OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration
end

-- Occurrences
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Law

variable {X Y : Type} [Fintype X] [Fintype Y]

def uniform (hx : 0 < Fintype.card X) : Law X where
  mass _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [hx.ne']

theorem sample (hx : 0 < Fintype.card X) (q : Law Y) (s : Finset X) {E : X × Y → Prop} {b : ℝ}
    (h : ∀ x ∈ s, b ≤ q.prob (fun y => E (x,y))) :
    s.card*b / Fintype.card X ≤ ((uniform hx).tensor q).prob E := by
  rw [tensor_prob]
  unfold mean
  calc
    _ = ∑ _ ∈ s, (Fintype.card X : ℝ)⁻¹*b := by simp; ring
    _ ≤ ∑ x ∈ s, (uniform hx).mass x * q.prob (fun y => E (x,y)) :=
      Finset.sum_le_sum fun x hx' => mul_le_mul_of_nonneg_left (h x hx') (by positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => mul_nonneg ((uniform hx).nonneg _) (q.positive _))

end Law

namespace Board.Naming

variable (u : Dials)



abbrev Sample := Radii u × u.History u.h × Table (u.Cell (NodeName u))

theorem radii_pos : 0 < Fintype.card (Radii u) := by rw [Fintype.card_fin]; exact Npos u

theorem colors_pos : 0 < Fintype.card (u.History u.h) := by rw [u.card_history]; positivity

def law (v : u.Valid) : Law (Sample u) :=
  (Law.uniform (radii_pos u)).tensor ((Law.uniform (colors_pos u)).tensor v.coin.law)

end Board.Naming

namespace Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid) (z : Sample u)

def Pass (i : X) := ∃ Q : Network u (NodeName u),
  (A.active z.1).Agree Q (A.name z.1) (Naming.P u) (R u) i ∧ Q.passes v z.2.1 z.2.2 (A.name z.1 i)

def Occurs (i : X) := L.w.Middle i ∧ L.w.live i ∧
  (∀ a, Network.Enrolled u u.h z.2.1 a → A.Earn v a (block u (u.phase a) z.1) (L.w.step i (u.side a))) ∧
  ∀ d, A.Pass v z (L.w.step i d)

variable {A v z}

theorem Pass.propagate {i : X} (h : A.Pass v z i) {Q : Network u (NodeName u)}
    (hq : (A.active z.1).Agree Q (A.name z.1) (Naming.P u) (Network.window u) i) :
    Q.passes v z.2.1 z.2.2 (A.name z.1 i) := by
  obtain ⟨Q',hh,hp⟩ := h
  have hr : Network.window u ≤ R u := by unfold R; omega
  have agree := (hh.cut hr).compare (e := Equiv.refl _) hq (fun _ _ => rfl)
  have hs := (Network.local_pass v z.2.1 agree z.2.2).mp hp
  simpa only [Dials.tables_id,Equiv.refl_apply] using hs

theorem dense_bin (safe : A.Safe) (fixed : A.Fixed) (v : u.Valid) {i : X} (hm : L.w.Middle i)
    (hl : L.w.live i) {r : Radii u} (hr : A.Good (L.w.step i) r) :
    ∃ c : u.History u.h, u.gamma*(u.rate u.h)^2 ≤ v.coin.law.prob (fun x => A.Occurs v (r,c,x) i) := by
  obtain ⟨Q,hQ⟩ := hr.model safe
  let key := fun d => A.name r (L.w.step i d)
  obtain ⟨c,hc⟩ := Q.color v key _ le_rfl
  have hh : ∀ d, L.w.layer (L.w.step i d) = Q.w.layer (key d) :=
    fun d => ((hQ d).cut (show 1 ≤ R u by unfold R; omega)).1
  have place : Q.w.place (key false) = Q.w.place (key true) := by
    unfold Board.place; rw [← hh,← hh]
    exact (L.w.middle_step hm hl false).2.trans (L.w.middle_step hm hl true).2.symm
  have ne : key false ≠ key true := by
    intro he
    have := (hh false).trans ((congrArg Q.w.layer he).trans (hh true).symm)
    have := L.w.east _ hl
    have := L.w.west _ hl
    omega
  refine ⟨c,(Q.pair v c place ne).trans (v.coin.law.mono ?_)⟩
  intro x hx
  refine ⟨hm,hl,fun a ha => hr.earn fixed v a _ (hQ _) (hc a ha),fun d => ⟨Q,hQ d,?_⟩⟩
  cases d
  · exact hx.1
  · exact hx.2

theorem dense (safe : A.Safe) (fixed : A.Fixed) (v : u.Valid) {i : X} (hm : L.w.Middle i)
    (hl : L.w.live i) {chance : ℕ} (hch : 0 < chance)
    (hsize : 2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2) :
    (chance : ℝ)⁻¹ ≤ (law u v).prob (fun z => A.Occurs v z i) := by
  let s := Finset.univ.filter (A.Good (L.w.step i))
  let q := (Law.uniform (colors_pos u)).tensor (v.coin (I := NodeName u)).law
  have hc : 0 < (chance : ℝ) := Nat.cast_pos.mpr hch
  have each : ∀ r ∈ s, 2/(chance : ℝ) ≤ q.prob (fun y => A.Occurs v (r,y) i) := by
    intro r hr
    obtain ⟨c,hh⟩ := dense_bin safe fixed v hm hl (Finset.mem_filter.mp hr).2
    have hb := Law.sample (colors_pos u) v.coin.law {c} (E := fun y => A.Occurs v (r,y) i)
      (b := u.gamma*(u.rate u.h)^2) (by simpa using hh)
    simp only [Finset.card_singleton,Nat.cast_one,one_mul] at hb
    apply le_trans _ hb
    rw [div_le_div_iff₀ hc (Nat.cast_pos.mpr (colors_pos u)),u.card_history]
    unfold Dials.count at hsize; linarith
  apply le_trans _ (Law.sample (radii_pos u) q s each)
  have large : (N u : ℝ) ≤ 2*s.card := by exact_mod_cast A.frequent (L.w.step i) fixed
  rw [le_div_iff₀ (Nat.cast_pos.mpr (radii_pos u)),Fintype.card_fin]
  rw [div_eq_mul_inv]; nlinarith only [mul_le_mul_of_nonneg_left large (inv_nonneg.mpr hc.le)]

end Board.Legs.Decoration
end OAI.Geometry.Hirsch.Layer
end

-- LiftTrip
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid) (z : Sample u)

def round : L.w.Round where
  mark i d := ∃ j, L.along i d j ∧ A.Occurs v z j
  middle := by
    rintro i d ⟨j,hj,_⟩
    exact ⟨(L.info _ _ _ hj).1,(L.info _ _ _ hj).2.1⟩
  jump i d j := L.along i d j ∧ j ≠ i
  localJump := by
    rintro i d j ⟨h,hn⟩
    obtain ⟨_,hl,_,he,_,hh⟩ := L.info _ _ _ h
    exact ⟨hl,he,hh.resolve_left hn⟩

variable {A v z} {Q : Network u (NodeName u)} {i : X} {d : Bool}

theorem marked (h : (A.round v z).mark i d) : A.Pass v z (L.w.step i d) := by
  obtain ⟨j,hj,ho⟩ := h
  rw [← (L.info _ _ _ hj).2.2.2.2.1]; exact ho.2.2.2 d

def Models (A : L.Decoration) (z : Sample u) (Q : Network u (NodeName u)) :=
  (A.active z.1).Agree Q (A.name z.1) (Naming.P u)

theorem marks (prom : ∀ i, A.Promised v i) (hq : A.Models z Q (Network.window u+2) i)
    (h : (A.round v z).mark i d) : (Q.done v z.2.1).round.mark (A.name z.1 i) d := by
  obtain ⟨j,hj,ho⟩ := h
  obtain ⟨hm,hl,_,_,he,_⟩ := L.info _ _ _ hj
  have hmid : Q.w.Middle (A.name z.1 i) := by unfold Middle; rw [← hq.1]; exact hm
  apply Q.marks v hmid (hq.2.1.mp hl)
  intro a ha
  have earn := ho.2.2.1 a ha
  have hp : u.phase a < Naming.P u := u.phase_lt a
  unfold Network.accepts
  split
  · rename_i eq
    subst d
    rw [he] at earn
    obtain ⟨eq,hh⟩ := hq.2.2.1 (u.side a) hl
    rw [← eq]
    exact earn _ rfl Q (hh.less hp.le (Nat.le_succ _))
  · rename_i hn
    have eq : d = !(u.side a) := by cases d <;> cases h : u.side a <;> simp_all
    obtain ⟨hl,he⟩ := prom i a z.1 j (eq ▸ hj) earn
    obtain ⟨eq,hh⟩ := hq.2.2.2 a hp
    rw [← eq]
    obtain ⟨eq',hh'⟩ := hh.2.2.1 (u.side a) hl
    exact ⟨hh.2.1.mp hl,eq' ▸ he _ rfl Q (hh'.less hp.le le_rfl)⟩

theorem lift_move {j : NodeName u} {k : ℕ} (hq : A.Models z Q (k+1) i)
    (hm : (Q.done v z.2.1).round.Move (A.name z.1 i) d j) :
    ∃ y, (A.round v z).Move i d y ∧ A.name z.1 y = j ∧ A.Models z Q k y := by
  have hl := hq.2.1.mpr hm.1
  rcases hm.2 with rfl | hj
  · exact ⟨_,(A.round v z).basic hl d,hq.2.2.1 d hl⟩
  have ne : j ≠ A.name z.1 i := fun he => ((Q.done v z.2.1).round.falls hm).ne (congrArg Q.w.rank he)
  obtain ⟨a,ha,hd,he⟩ := Q.final_fits v _ _ _ _ hj
  obtain ⟨hh,ht⟩ := hq.2.2.2 a ha
  have eq : A.name z.1 ((A i).slot a z.1) = j := hh.trans he
  have hn : (A i).slot a z.1 ≠ i := fun h => ne (eq.symm.trans (congrArg _ h))
  have along := ((A i).valid a z.1).resolve_left hn
  exact ⟨_,⟨hl,.inr ⟨hd.symm ▸ along,hn⟩⟩,eq,ht⟩

theorem lift_trip (prom : ∀ i, A.Promised v i) {b : Budget} {x y : NodeName u} {path : List (NodeName u)} {s : ℕ}
    (ht : (Q.done v z.2.1).round.Trip Set.univ x y b path) (dead : ¬Q.w.live y)
    (allow : ∀ g ∈ path, Q.passes v z.2.1 z.2.2 g → Q.w.place g = s)
    (he : A.name z.1 i = x) (hq : A.Models z Q (Network.window u+2+Network.total u b) i) :
    ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j b l ∧ ∀ g ∈ l, L.w.place g = s := by
  induction ht generalizing i with
  | nil =>
    have hh := Network.Agree.cut hq (show 1 ≤ _ by omega)
    exact ⟨i,[],fun hl => dead (he ▸ hh.2.1.mp hl),.nil,by simp⟩
  | @go x y endpt d b a path hi hm ha ht ih =>
    subst x
    have spend := Network.total_spend (u := u) (Q.w.bound _) ha
    have hh := Network.Agree.cut hq (show Network.window u+2+Network.total u a+1 ≤ _ by omega)
    obtain ⟨j,hj,he,hq'⟩ := lift_move hh hm
    obtain ⟨k,l,hdead,ht,hgood⟩ := ih dead (fun _ h => allow _ (List.mem_append_right _ h)) he hq'
    refine ⟨k,_,hdead,.go (Set.mem_univ _) hj (hh.1.symm ▸ ha) ht,?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    swap
    · exact hgood _ hg
    obtain ⟨hc,rfl⟩ := (A.round v z).charge_mem.mp hg
    obtain ⟨key,hkey⟩ := hh.2.2.1 d hj.1
    have hm := marks prom (hh.cut (by omega)) hc
    have hp := (marked hc).propagate (hkey.cut (by omega))
    have heq := (hkey.cut (show 1 ≤ _ by omega)).place
    exact heq.trans (allow _ (List.mem_append_left _ ((Q.done v z.2.1).round.charge_mem.mpr ⟨hm,key⟩)) hp)

theorem Pass.path (hp : A.Pass v z i) (prom : ∀ i, A.Promised v i) :
    ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j (flat (u.D u.h).step) l ∧
      ∀ g ∈ l, L.w.place g = L.w.place i := by
  obtain ⟨Q,hq,hh⟩ := hp
  have hn : u.a^u.h ≤ u.a^(u.h+1) := Nat.pow_le_pow_right (by have := v.base; omega) (by omega)
  obtain ⟨_,_,hd,ht,ha⟩ := Stage.final_path hn hh
  have eq := (hq.cut (show 1 ≤ R u by unfold R; omega)).place
  exact lift_trip prom ht hd (fun _ hg hp => (ha _ hg hp).trans eq.symm) rfl
    (hq.cut (Nat.add_le_add_left (Network.total_le u le_rfl) _))

theorem escape (prom : ∀ i, A.Promised v i) (z : Sample u) (hi : L.w.Shore d i) :
    ∃ s ≠ L.w.place i, ∃ j l, ¬L.w.live j ∧ (A.round v z).Trip Set.univ i j (flat (1+(u.D u.h).step)) l ∧
      ∀ g ∈ l, L.w.place g = s := by
  let r := A.round v z
  obtain ⟨l,⟨j,he,ht⟩,ho⟩ := r.spine (Set.mem_univ (L.w.place i)) d
  have hd := (he.resolve_right fun h => h.1 (Set.mem_univ _)).2
  cases l with
  | nil => exact ⟨L.w.place i+1,by omega,j,[],hd,ht.more (fun _ => Nat.le_add_right ..),by simp⟩
  | cons g tail =>
    have h := ho g (by simp)
    have hn := (h.strict hi).ne'
    obtain ⟨u',_,_,hm,he⟩ := h
    obtain ⟨k,l,hd,hh,hs⟩ := (he ▸ marked hm).path prom
    have pre : r.Trip Set.univ i g (flat 1) [g] := Round.Trip.redirect (pre := []) ht
    exact ⟨L.w.place g,fun e => hn ((L.w.same d _ _).mpr e),k,_,hd,pre.append hh,by simpa using hs⟩

end OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration
end

-- Compressed
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Compression

def offset (width l : ℕ) := if width ∣ l then 0 else if width ∣ l+1 then 2 else 1

def code (width base l : ℕ) := 3*(l/width%base)+offset width l

theorem adjacent (width base l : ℕ) (hw : 3 ≤ width) (same : (l+1)/width/base = l/width/base) :
    (offset width l = 1 ∧ offset width (l+1) = 1) ∨ code width base l + 1 = code width base (l+1) := by
  have avoid : ∀ x y, 0 < y → y < width → width ∣ x → ¬width ∣ x+y := by
    intro x y hp hs hx he
    have hd : width ∣ y := by simpa using Nat.dvd_sub he hx
    exact hs.not_ge (Nat.le_of_dvd hp hd)
  by_cases hb : width ∣ l+1
  · have hn : ¬width ∣ l := fun hh => avoid l 1 (by omega) (by omega) hh hb
    have h₁ := Nat.mod_add_div ((l+1)/width) base
    have h₂ := Nat.mod_add_div (l/width) base
    rw [same] at h₁
    have h₃ := Nat.succ_div_of_dvd hb
    right; simp only [code,offset,if_pos hb,if_neg hn]; omega
  have h := Nat.succ_div_of_not_dvd hb
  by_cases ha : width ∣ l
  · have hn : ¬width ∣ l+1+1 := avoid l 2 (by omega) (by omega) ha
    right; simp [code,offset,h,hb,ha,hn]
  by_cases hc : width ∣ l+1+1
  · right; simp [code,offset,h,hb,ha,hc]
  · left; simp [offset,ha,hb,hc]

end Compression

namespace World

open Compression

variable {X : Type} {n : ℕ} (w : World X n) (width base : ℕ)

abbrev Compressed (X : Type) := X ⊕ (X × Bool)

def index (x : X) := w.block width x % base

def height : Compressed X → ℕ
  | .inl x => code width base (w.layer x)
  | .inr (x,d) => 3*w.index width base x + if d then 2 else 0

def rankPlus : Compressed X → ℕ
  | .inl x => w.rank x+1
  | .inr _ => 0

def awake : Compressed X → Prop
  | .inl x => ¬w.Blank width x ∨ w.live x ∧ ¬w.Blank (width*base) x
  | .inr _ => False

def finish (d : Bool) (x : X) : Compressed X :=
  if w.Blank width x then .inl x else if _h : w.live x then finish d (w.step x d) else .inr (x,d)
termination_by w.rank x
decreasing_by exact w.decrease _ _h _

def dest (i : Compressed X) (d : Bool) : Compressed X :=
  match i with
  | .inl x => if w.Blank width x then .inl (w.step x d) else w.finish width d x
  | .inr _ => i

theorem height_real (x : X) : w.height width base (.inl x) =
    3*w.index width base x + offset width (w.layer x) := rfl

theorem offset_mid (x : X) : offset width (w.layer x) = 1 ↔ ¬w.Blank width x := by
  unfold offset Blank; split_ifs <;> simp_all

theorem offset_small (x : X) : offset width (w.layer x) < 3 := by unfold offset; split_ifs <;> omega

theorem adj {x : X} (hw : 3 ≤ width) (hl : w.live x) (d : Bool)
    (hs : w.block (width*base) (w.step x d) = w.block (width*base) x)
    (hb : w.Blank width x ∨ w.Blank width (w.step x d)) :
    if d then w.height width base (.inl (w.step x d)) = w.height width base (.inl x)+1
    else w.height width base (.inl (w.step x d))+1 = w.height width base (.inl x) := by
  have hn : ¬(offset width (w.layer x) = 1 ∧ offset width (w.layer (w.step x d)) = 1) := by
    rw [w.offset_mid,w.offset_mid]; tauto
  simp only [block,← Nat.div_div_eq_div_mul] at hs
  cases d
  · have he := w.west _ hl
    have hh := adjacent width base (w.layer (w.step x false)) hw (by rw [he]; exact hs.symm)
    rw [he] at hh; exact hh.resolve_left (fun h => hn h.symm)
  · have he := w.east _ hl
    have hh := adjacent width base (w.layer x) hw (by rw [← he]; exact hs)
    rw [← he] at hh; exact (hh.resolve_left hn).symm

theorem finished (hw : 3 ≤ width) (d : Bool) : ∀ x, ¬w.Blank width x →
    w.height width base (w.finish width d x) = 3*w.index width base x + (if d then 2 else 0) ∧
      w.rankPlus (w.finish width d x) < w.rank x+1 := by
  apply w.induct
  intro x ih hn
  rw [finish,if_neg hn]
  split
  swap
  · exact ⟨rfl,Nat.zero_lt_succ _⟩
  rename_i hl
  have hs := w.same_step hl hn d
  have hindex : w.index width base (w.step x d) = w.index width base x := congrArg (· % base) hs
  have hdec := w.decrease _ hl d
  by_cases hb : w.Blank width (w.step x d)
  · rw [finish,if_pos hb]
    have h := w.adj width base hw hl d (by simp only [parent,hs]) (.inr hb)
    rw [w.height_real width base x,(w.offset_mid width x).mpr hn] at h
    refine ⟨?_,Nat.succ_lt_succ hdec⟩
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;> omega
  obtain ⟨he,ht⟩ := ih hl d hb
  exact ⟨by rw [he,hindex],ht.trans (Nat.succ_lt_succ hdec)⟩

theorem destination (hw : 3 ≤ width) (i : Compressed X) (hl : w.awake width base i) (d : Bool) :
    (if d then w.height width base (w.dest width i d) = w.height width base i + 1
      else w.height width base (w.dest width i d)+1 = w.height width base i) ∧
    w.rankPlus (w.dest width i d) < w.rankPlus i := by
  rcases i with x | t
  swap
  · exact hl.elim
  by_cases hb : w.Blank width x
  · obtain ⟨hl,hn⟩ := hl.resolve_left (not_not.mpr hb)
    rw [dest,if_pos hb]
    exact ⟨w.adj width base hw hl d (w.same_step hl hn d) (.inl hb),Nat.succ_lt_succ (w.decrease _ hl d)⟩
  rw [dest,if_neg hb]
  obtain ⟨he,ht⟩ := w.finished width base hw d x hb
  refine ⟨?_,ht⟩
  rw [he,w.height_real,(w.offset_mid width x).mpr hb]
  cases d <;> simp

def board (hw : 3 ≤ width) (hb : 0 < base) : Board (Compressed X) base where
  layer := w.height width base
  live := w.awake width base
  rank := w.rankPlus
  step := w.dest width
  bound := by
    rintro (x | ⟨x,d⟩)
    · rw [height_real]; have := w.offset_small width x; have : w.index width base x < base := Nat.mod_lt _ hb; omega
    · have : w.index width base x < base := Nat.mod_lt _ hb
      simp only [height]; split <;> omega
  west i hl := (w.destination width base hw i hl false).1
  east i hl := (w.destination width base hw i hl true).1
  decrease i hl d := (w.destination width base hw i hl d).2

end World
end OAI.Geometry.Hirsch.Layer
end

-- Legs
noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

open Board

variable {X : Type} {n : ℕ} (w : World X n) (width : ℕ)

inductive Leg (d : Bool) : X → X → Prop
  | here {x} (hm : ¬w.Blank width x) : Leg d x x
  | go {x y} (hm : ¬w.Blank width x) (hl : w.live x) (ht : Leg d (w.step x d) y) : Leg d x y

variable {w width} {x y : X} {d : Bool}

theorem Leg.info (h : w.Leg width d x y) : ¬w.Blank width x ∧ ¬w.Blank width y ∧
    w.block width y = w.block width x ∧ w.finish width d y = w.finish width d x ∧
    (y = x ∨ w.rank y < w.rank x) := by
  induction h with
  | here hm => exact ⟨hm,hm,rfl,rfl,.inl rfl⟩
  | go hm hl ht ih =>
    obtain ⟨_,hy,hb,he,hr⟩ := ih
    refine ⟨hm,hy,hb.trans (w.same_step hl hm d),?_,.inr ?_⟩
    · exact he.trans (by conv_rhs => rw [finish,if_neg hm,dif_pos hl])
    · exact (hr.elim (fun h => (congrArg w.rank h).le) LT.lt.le).trans_lt (w.decrease _ hl d)

variable (w width) (base : ℕ) (hw : 3 ≤ width) (hb : 0 < base)

theorem at_real (x : X) : (w.board width base hw hb).place (.inl x) = w.index width base x := by
  change w.height width base (.inl x)/3 = _
  rw [w.height_real]; have := w.offset_small width x; omega

theorem mid_real (x : X) : (w.board width base hw hb).Middle (.inl x) ↔ ¬w.Blank width x := by
  change w.height width base (.inl x)%3 = 1 ↔ _
  rw [w.height_real,← w.offset_mid]
  have := w.offset_small width x; omega

theorem shore_real (hm : w.Blank width x) : ∃ d, (w.board width base hw hb).Shore d (.inl x) := by
  have hh := (w.mid_real width base hw hb x).not.mpr (not_not.mpr hm)
  unfold Middle at hh
  by_cases h : (w.board width base hw hb).layer (.inl x)%3 = 2
  · exact ⟨true,h⟩
  · exact ⟨false,by unfold Shore; simp; omega⟩

def along : Compressed X → Bool → Compressed X → Prop
  | .inl x,d,.inl y => w.Leg width d x y
  | _,_,_ => False

variable {u : Dials}

def legs (v : u.Valid) (hw : 3 ≤ width) : Board.Legs u (Compressed X) where
  w := w.board width (u.a^u.h) hw (pow_pos (lt_of_lt_of_le (by decide : 0 < 2) v.base) _)
  along := w.along width
  info := by
    rintro (x | x) d (y | y) h <;> try exact h.elim
    obtain ⟨hx,hy,he,hf,hr⟩ := Leg.info h
    refine ⟨(w.mid_real ..).mpr hx,.inl hx,.inl hy,?_,?_,?_⟩
    · change w.height width (u.a^u.h) (.inl y) = w.height width (u.a^u.h) (.inl x)
      rw [height_real,height_real,(w.offset_mid _ _).mpr hx,(w.offset_mid _ _).mpr hy]
      simp only [index,he]
    · simpa only [board,dest,if_neg hx,if_neg hy] using hf
    · exact hr.imp (congrArg Sum.inl) Nat.succ_lt_succ

def Allowed (occ : X → Prop) (par site : ℕ) (i : X) :=
  w.block (width*base) i = par ∧ (occ i → w.index width base i = site)

def Stop (i : X) := ¬w.live i ∨ w.Blank (width*base) i

def Resume (occ : X → Prop) (par site : ℕ) (d : Bool) (k : ℕ) : Compressed X → Prop
  | .inl i => w.block (width*base) i = par →
      w.Walk (w.Allowed width base occ par site) (w.Stop width base) i d k
  | .inr _ => True

def Permitted (occ : X → Prop) (site : ℕ) (d : Bool) (x : X) :=
  ∀ y, w.Leg width d x y → occ y → w.index width base y = site

variable {w width base} {occ : X → Prop} {par site k : ℕ}

theorem Permitted.next (h : w.Permitted width base occ site d x) (hm : ¬w.Blank width x) (hl : w.live x) :
    w.Permitted width base occ site d (w.step x d) := fun _ ht => h _ (.go hm hl ht)

theorem Leg.expand (h : w.Leg width d x y) (ok : w.Permitted width base occ site d x)
    (ht : w.Resume width base occ par site d k (.inl y)) : w.Resume width base occ par site d k (.inl x) := by
  induction h with
  | here => exact ht
  | go hm hl h ih =>
    intro hp
    have hp' := (w.same_step hl (fun hh => hm (w.blank_mono (dvd_mul_right ..) hh)) d).trans hp
    exact .go ⟨hp,ok _ (.here hm)⟩ hl (by simp [turn]) (ih (ok.next hm hl) ht hp')

theorem expand_finish (w : World X n) (d : Bool) : ∀ x, w.Permitted width base occ site d x →
    w.Resume width base occ par site d k (w.finish width d x) → w.Resume width base occ par site d k (.inl x) := by
  apply w.induct
  intro x ih ok ht
  rw [finish] at ht
  split at ht
  · exact ht
  rename_i hm
  intro hp
  have good : w.Allowed width base occ par site x := ⟨hp,ok _ (.here hm)⟩
  split at ht
  · rename_i hl
    have hp' := (w.same_step hl (fun hh => hm (w.blank_mono (dvd_mul_right ..) hh)) d).trans hp
    exact .go good hl (by simp [turn]) (ih hl d (ok.next hm hl) ht hp')
  · exact .done good (.inl ‹_›)

theorem expand_dest (blank : ∀ x, w.Blank width x → ¬occ x) (hl : w.awake width base (.inl x))
    (ok : w.Permitted width base occ site d x) (ht : w.Resume width base occ par site d k (w.dest width (.inl x) d)) :
    w.Resume width base occ par site d k (.inl x) := by
  rw [dest] at ht
  split at ht
  · rename_i hb
    obtain ⟨hl,hn⟩ := hl.resolve_left (not_not.mpr hb)
    intro hp
    exact .go ⟨hp,fun h => (blank _ hb h).elim⟩ hl (by simp [turn]) (ht ((w.same_step hl hn d).trans hp))
  · exact w.expand_finish d _ ok ht

end OAI.Geometry.Hirsch.Layer.World
end

-- Potential
noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.World

open Board Naming

variable {X : Type} {n : ℕ} {u : Dials} {v : u.Valid} {w : World X n} {width : ℕ} {hw : 3 ≤ width}
  (A : (w.legs width v hw).Decoration) (z : Sample u)

def occurs (x : X) := A.Occurs v z (.inl x)

theorem blank_free (x : X) (hb : w.Blank width x) : ¬occurs A z x :=
  fun hh => (w.mid_real width (u.a^u.h) hw (pow_pos (by have := v.base; omega) _) x).mp hh.1 hb

theorem permits {x : X} {d : Bool} {s : ℕ}
    (hh : ∀ g ∈ (A.round v z).charge (.inl x) d, (w.legs width v hw).w.place g = s) :
    w.Permitted width (u.a^u.h) (occurs A z) s d x := by
  intro y hy ho
  let r := A.round v z
  let b := (w.legs width v hw).w
  have hm : r.mark (.inl x) d := ⟨.inl y,hy,ho⟩
  have key := hh _ (r.charge_mem.mpr ⟨hm,rfl⟩)
  have eq := (b.middle_step (r.middle _ _ hm).1 (r.middle _ _ hm).2 d).2
  have he : b.place (.inl x) = w.index width (u.a^u.h) x := w.at_real width (u.a^u.h) hw (pow_pos (by have := v.base; omega) _) x
  exact (congrArg (· % (u.a^u.h)) hy.info.2.2.1).trans (he.symm.trans (eq.symm.trans key))

theorem expand {i j : Compressed X} {b : Budget} {path : List (Compressed X)} {par s : ℕ}
    (ht : (A.round v z).Trip Set.univ i j b path) (hd : ¬(w.legs width v hw).w.live j)
    (hh : ∀ g ∈ path, (w.legs width v hw).w.place g = s) :
    ∀ e, w.Resume width (u.a^u.h) (occurs A z) par s e (Board.Network.total u b) i := by
  induction ht with
  | @nil i b =>
    intro e
    rcases i with x | t
    swap
    · exact True.intro
    have hb : w.Blank width x := by_contra (fun h => hd (.inl h))
    have hs : w.Stop width (u.a^u.h) x := by
      by_cases hl : w.live x
      · exact .inr (by_contra fun hn => hd (.inr ⟨hl,hn⟩))
      · exact .inl hl
    exact fun hp => .done ⟨hp,fun h => (blank_free A z _ hb h).elim⟩ hs
  | @go i j k d b a path hi hm ha ht ih =>
    have cost := Board.Network.total_spend (u := u) ((w.legs width v hw).w.bound _) ha
    have tail := ih hd (fun _ h => hh _ (List.mem_append_right _ h)) d
    intro e
    rcases i with x | t
    swap
    · exact True.intro
    have ok := permits A z (fun _ h => hh _ (List.mem_append_left _ h))
    have walk : w.Resume width (u.a^u.h) (occurs A z) par s d (Board.Network.total u a) (.inl x) := by
      rcases hm with ⟨hl,rfl | hj⟩
      · exact expand_dest (blank_free A z) hl ok tail
      · rcases j with y | t
        · exact Leg.expand hj.1 ok tail
        · exact hj.1.elim
    exact fun hp => ((walk hp).redirect e).more cost

def turns (u : Dials) := Board.Network.size u*(1+(u.D u.h).step)

theorem potential (v : u.Valid) (w : World X n) (width : ℕ) (hw : 3 ≤ width) {chance : ℕ}
    (hch : 0 < chance) (hsize : 2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2) :
    Nonempty (w.Potential (law u v) chance (turns u) width (u.a^u.h)) := by
  let base := u.a^u.h
  have hb : 0 < base := pow_pos (by have := v.base; omega) _
  let L := w.legs width v hw
  obtain ⟨A,safe,fixed,prom⟩ := Board.Legs.Decoration.exists_decoration L v
  refine ⟨⟨fun x => {z | occurs A z x},?_,?_⟩⟩
  · intro x hx
    exact Board.Legs.Decoration.dense safe fixed v ((w.mid_real width base hw hb x).mpr hx) (.inl hx) hch hsize
  intro x hx z
  obtain ⟨d,hd⟩ := w.shore_real width base hw hb hx
  obtain ⟨s,hs,j,l,hdead,ht,hh⟩ := Board.Legs.Decoration.escape prom z hd
  let par := w.block (width*base) x
  have h := expand A z (par := par) ht hdead hh false rfl
  have one : ∀ y, w.block (width*base) y = par → w.index width base y + base*par = w.block width y := by
    intro y he
    rw [← he,w.parent]; exact Nat.mod_add_div _ _
  have he : L.w.place (.inl x) = w.index width base x := w.at_real width base hw hb x
  refine ⟨s + base*par,fun h => hs (by rw [he]; have := one x rfl; omega),?_⟩
  refine (h.more (Board.Network.total_le u le_rfl)).mono ?_ (fun _ h => h)
  rintro y ⟨hy,ho⟩
  exact ⟨hy,fun hh => (one y hy).symm.trans (congrArg (· + base*par) (ho hh))⟩

end OAI.Geometry.Hirsch.Layer.World

namespace OAI.Geometry.Hirsch.Layer

theorem primary : PrimaryLemma := by
  intro m hm
  obtain ⟨u,b,bits,chance,v,hb,hi,hc,he,hkey,hs,hsize⟩ := Dials.choose m hm
  refine ⟨b,bits,chance,World.turns u,hb,hi,hc,hkey,hs,Board.Naming.Sample u,inferInstance,Board.Naming.law u v,?_⟩
  rw [he]
  exact fun _ _ w width hw => w.potential v width hw hc hsize

end OAI.Geometry.Hirsch.Layer
end


noncomputable section
namespace OAI.Geometry.Hirsch.Layer.Palette
open World
variable {X α : Type} {L k b D n : ℕ}

/-- Simultaneous interpolation. Fuel bounds the cost of every candidate escape,
not the depth of either endpoint tree. -/
theorem middle {w : World X n} (hw : w.Full) {ι : Type} (ok : ι → X → Prop)
    {x y : X} (hx : ∀ l e, ¬ w.Escape (ok l) x e D)
    (hy : ∀ l e, ¬ w.Escape (ok l) y e D)
    {j : ℕ} (hj : w.layer x ≤ j) (hj' : j ≤ w.layer y) :
    ∃ z, w.layer z = j ∧ ∀ l e, ¬ w.Escape (ok l) z e D := by
  have aux (f j : ℕ) (ha : w.layer x ≤ j) (hb : j ≤ w.layer y) :
      ∃ z, w.layer z = j ∧ ∀ l e m, m ≤ D → cost n j e m < f → ¬ w.Escape (ok l) z e m := by
    induction f generalizing j with
    | zero =>
      obtain ⟨z,hz⟩ := hw.1 j (hb.trans_lt (w.bound y))
      exact ⟨z,hz,by intros; omega⟩
    | succ f ih =>
      by_cases ha' : w.layer x = j
      · exact ⟨x,ha',fun l e m hm _ h => hx l e (h.more hm)⟩
      by_cases hb' : w.layer y = j
      · exact ⟨y,hb',fun l e m hm _ h => hy l e (h.more hm)⟩
      obtain ⟨u,hu,hu'⟩ := ih (j-1) (by omega) (by omega)
      obtain ⟨v,hv,hv'⟩ := ih (j+1) (by omega) (by omega)
      obtain ⟨z,hl,hwst,hest⟩ := hw.2 u v (by omega)
      have hz := w.east z hl
      rw [hest,hv] at hz
      have hze : w.layer z = j := by omega
      refine ⟨z,hze,?_⟩
      intro l e m hm hf h
      cases h with
      | done _ hn => exact hn hl
      | go hg hLive hbud htail =>
        have hstep := cost_step hl hbud
        rw [hze] at hstep
        rename_i dir t
        have ht : t ≤ D := by omega
        cases dir
        · rw [hwst,hu] at hstep
          exact hu' l false t ht (by omega) (hwst ▸ htail)
        · rw [hest,hv] at hstep
          exact hv' l true t ht (by omega) (hest ▸ htail)
  obtain ⟨z,hz,hh⟩ := aux (D*n+n) j hj hj'
  refine ⟨z,hz,fun l e => hh l e D le_rfl ?_⟩
  have hd := w.distance_lt z e
  rw [hz] at hd
  exact Nat.add_lt_add_left hd _

variable [Fintype α] [DecidableEq α] {w : World X (L*(k+2))}
variable (p : w.Emissions (Fin b) D) (W : Fin L → Finset α)
def avoids (q : Fin b × α) (x : X) := p.emit x = some q.1 → q.2 ∉ W (w.site x)
def Z (x : X) : Finset (Fin b × α) := by
  classical
  exact Finset.univ.filter (fun q => ∀ e, ¬ w.Escape (avoids p W q) x e D)
omit [DecidableEq α] in
@[simp] theorem mem_Z {x : X} {q : Fin b × α} : q ∈ Z p W x ↔ ∀ e, ¬ w.Escape (avoids p W q) x e D := by classical simp [Z]
omit [DecidableEq α] in
theorem home {x : X} {i : Fin b} (he : p.emit x = some i) :
    ({i} : Finset _ ) ×ˢ W (w.site x) ⊆ Z p W x := by
  rintro ⟨j,a⟩ ha
  obtain ⟨rfl,ha'⟩ : j = i ∧ a ∈ W (w.site x) := by simpa [and_comm, eq_comm] using ha
  exact (mem_Z p W).mpr fun _ h => h.good he ha'

omit [Fintype α] [DecidableEq α] in
theorem ray (i : Fin b) (e : Bool) : ∀ x, ∃ s : Fin L,
    (if e then w.site x ≤ s else s ≤ w.site x) ∧
    ∀ a, a ∉ W s → w.Escape (avoids p W (i,a)) x e D := by
  apply w.induct
  intro x ih
  by_cases h : p.emit x = some i
  · refine ⟨w.site x,by simp,fun a ha => (p.escape x i h e).mono ?_ (fun _ h => h)⟩
    exact fun y hy hem => (hy hem).symm ▸ ha
  by_cases hl : w.live x
  · obtain ⟨s,hs,hh⟩ := ih hl e
    refine ⟨s,?_,fun a ha => .go (fun he => (h he).elim) hl (by simp [turn]) (hh a ha)⟩
    cases e
    · exact le_trans hs (Nat.div_le_div_right (by have := w.west x hl; omega))
    · exact le_trans (Nat.div_le_div_right (by have := w.east x hl; omega)) hs
  · exact ⟨w.site x,by simp,fun _ _ => .done (fun he => (h he).elim) hl⟩

theorem cross {r : ℕ} (hr : ∀ s t, s ≠ t → (W s ∩ W t).card ≤ r)
    {x y : X} (hxy : w.site x < w.site y) : (Z p W x ∩ Z p W y).card ≤ b*r := by
  classical
  let C := Z p W x ∩ Z p W y
  have H := Finset.card_le_mul_card_image_of_maps_to (s := C) (t := Finset.univ)
    (f := Prod.fst) (fun _ _ => Finset.mem_univ _) r
  suffices h : ∀ i : Fin b, (C.filter (fun q => q.1 = i)).card ≤ r by
    simpa [C,Nat.mul_comm] using H (fun i _ => h i)
  intro i
  obtain ⟨s,hs,hs'⟩ := ray p W i false x
  obtain ⟨t,ht,ht'⟩ := ray p W i true y
  have hst : s < t := lt_of_le_of_lt hs (lt_of_lt_of_le hxy ht)
  apply le_trans _ (hr s t hst.ne)
  apply Finset.card_le_card_of_injOn Prod.snd
  · rintro ⟨j,a⟩ h
    obtain ⟨hc,rfl⟩ := Finset.mem_filter.mp h
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hc
    exact Finset.mem_inter.mpr ⟨by by_contra hn; exact (mem_Z p W).mp hx false (hs' _ hn),
      by by_contra hn; exact (mem_Z p W).mp hy true (ht' _ hn)⟩
  · rintro ⟨j,a⟩ hj ⟨k,c⟩ hk he
    exact Prod.ext ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm) he

def family (j : Fin k) (d : ℕ) (s : Fin L) : Finset (Finset (Fin b × α)) := by
  classical
  exact Finset.univ.filter (fun A => A.card = d ∧ ∃ x, w.layer x = micro s j ∧ A ⊆ Z p W x)
omit [DecidableEq α] in
@[simp] theorem mem_family {j d s A} : A ∈ family p W j d s ↔
    A.card = d ∧ ∃ x, w.layer x = micro s j ∧ A ⊆ Z p W x := by classical simp [family]

omit [DecidableEq α] in
theorem capacity {d : ℕ} (hd : ∀ s, (W s).card = d) {j : Fin k} {s : Fin L} {x : X}
    (hx : w.layer x = micro s j) : d ≤ (Z p W x).card := by
  obtain ⟨i,hi⟩ := p.micro s j x hx
  simpa [hd] using Finset.card_le_card (home p W hi)

theorem families (hw : w.Full) (j : Fin k) {r d : ℕ} (hd : ∀ s, (W s).card = d)
    (hr : ∀ s t, s ≠ t → (W s ∩ W t).card ≤ r) (hgap : b*r < d) :
    let F := family p W j d
    (∀ s, (F s).Nonempty) ∧ (∀ s A, A ∈ F s → A.card = d) ∧
    (∀ s t, s ≠ t → Disjoint (F s) (F t)) ∧
    (∀ s u t, s ≤ u → u ≤ t → ∀ A ∈ F s, ∀ B ∈ F t,
      ∃ M ∈ F u, A ∩ B ⊆ M) := by
  classical
  dsimp only
  refine ⟨?_, fun s A h => ((mem_family p W).mp h).1, ?_, ?_⟩
  · intro s
    obtain ⟨x,hx⟩ := hw.1 _ (micro_bound s j)
    obtain ⟨A,hA,hEq⟩ := Finset.exists_subset_card_eq (capacity p W hd hx)
    exact ⟨A,(mem_family p W).mpr ⟨hEq,x,hx,hA⟩⟩
  · intro s t hne
    rw [Finset.disjoint_left]
    intro A hA hB
    obtain ⟨he,x,hx,hA⟩ := (mem_family p W).mp hA
    obtain ⟨_,y,hy,hB⟩ := (mem_family p W).mp hB
    have f {x y : X} (hxy : w.site x < w.site y) (hA : A ⊆ Z p W x) (hB : A ⊆ Z p W y) : False := by
      have h := (Finset.card_le_card (Finset.subset_inter hA hB)).trans (cross p W hr hxy)
      omega
    rcases lt_or_gt_of_ne hne with h | h
    · exact f (by rwa [w.site_micro hx,w.site_micro hy]) hA hB
    · exact f (by rwa [w.site_micro hy,w.site_micro hx]) hB hA
  · intro s u t hsu hut A hA B hB
    obtain ⟨he,x,hx,hA⟩ := (mem_family p W).mp hA
    obtain ⟨_,y,hy,hB⟩ := (mem_family p W).mp hB
    have mon {s u : Fin L} (h : s ≤ u) : micro s j ≤ micro u j := by
      unfold micro; gcongr; exact h
    let C := A ∩ B
    obtain ⟨z,hz,hz'⟩ := middle hw (fun q : C => avoids p W q.val)
      (x := x) (y := y) (fun q => (mem_Z p W).mp (hA (Finset.mem_inter.mp q.prop).1))
      (fun q => (mem_Z p W).mp (hB (Finset.mem_inter.mp q.prop).2))
      (j := micro u j) (hx ▸ mon hsu) (hy ▸ mon hut)
    have hC : C ⊆ Z p W z := fun q hq => (mem_Z p W).mpr (hz' ⟨q,hq⟩)
    obtain ⟨M,hCM,hM,hEq⟩ := Finset.exists_subsuperset_card_eq hC
      (he ▸ Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := B))) (capacity p W hd hz)
    exact ⟨M,(mem_family p W).mpr ⟨hEq,z,hz,hM⟩,hCM⟩

/-- Width-one free-world specialization for the palette construction. -/
theorem free_families (L b D : ℕ) (p : (free (L*(1+2))).Emissions (k := 1) (Fin b) D)
    (W : Fin L → Finset α) {d r : ℕ} (hd : ∀ s, (W s).card = d)
    (hr : ∀ s t, s ≠ t → (W s ∩ W t).card ≤ r) (hgap : b*r < d) :
    ∃ F : Fin L → Finset (Finset (Fin b × α)),
    (∀ s, (F s).Nonempty) ∧ (∀ s A, A ∈ F s → A.card = d) ∧
    (∀ s t, s ≠ t → Disjoint (F s) (F t)) ∧
    (∀ s u t, s ≤ u → u ≤ t → ∀ A ∈ F s, ∀ B ∈ F t,
      ∃ M ∈ F u, A ∩ B ⊆ M) :=
  ⟨_,families p W (full_free _) 0 hd hr hgap⟩

end OAI.Geometry.Hirsch.Layer.Palette

namespace StrictLayerCode
open Polynomial

private def graph {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (f : Polynomial K) : Finset (K × K) :=
  Finset.univ.image fun x => (x, f.eval x)

private theorem onGraph {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {f : Polynomial K} {z : K × K} (hz : z ∈ graph f) : f.eval z.1 = z.2 := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  rfl

private theorem overlap {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (f g : degreeLT K 6) (hne : f ≠ g) : (graph f.val ∩ graph g.val).card ≤ 5 := by
  let q := f.val - g.val
  have hq : q ≠ 0 := sub_ne_zero.mpr (fun h => hne (Subtype.ext h))
  have deg : q.degree < (6 : ℕ) := mem_degreeLT.mp ((degreeLT K 6).sub_mem f.property g.property)
  have small := (natDegree_lt_iff_degree_lt hq).2 deg
  calc
    _ ≤ q.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro z hz
        obtain ⟨hf, hg⟩ := Finset.mem_inter.mp hz
        apply Multiset.mem_toFinset.mpr
        apply (mem_roots hq).mpr
        exact (show q.eval z.1 = 0 by simp [q, onGraph hf, onGraph hg])
      · intro z hz w hw h
        exact Prod.ext h ((onGraph (Finset.mem_inter.mp hz).1).symm.trans
          ((congrArg f.val.eval h).trans (onGraph (Finset.mem_inter.mp hw).1)))
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := card_roots' _
    _ ≤ 5 := by omega

/-- Polynomial graphs give constant-size words of bounded pairwise overlap. -/
theorem exists_words (b : ℕ) (hb : 1000 ≤ b) :
    ∃ (α : Type) (_ : Fintype α) (_ : DecidableEq α) (W : Fin (b^6) → Finset α) (d : ℕ),
      (∀ s, (W s).card = d) ∧ (∀ s t, s ≠ t → (W s ∩ W t).card ≤ 5) ∧
      5*b < d ∧ d * (b * Fintype.card α - 1) + 1 < b^6 := by
  classical
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (5*b) (by omega)
  let : Fact p.Prime := ⟨hp⟩
  let K := ZMod p
  have hbp : b ≤ p := by omega
  have hc : Fintype.card (Fin (b^6)) ≤ Fintype.card (Fin 6 → K) := by
    simp only [Fintype.card_fin, Fintype.card_fun, K, ZMod.card]
    exact Nat.pow_le_pow_left hbp 6
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let P (s : Fin (b^6)) := (degreeLTEquiv K 6).symm (e s)
  refine ⟨K × K, inferInstance, inferInstance, fun s => graph (P s).val, p, ?_, ?_, hlo, ?_⟩
  · intro s
    change (graph (P s).val).card = p
    unfold graph
    rw [Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
    simp [K, ZMod.card]
  · intro s t h
    exact overlap _ _ (fun eq => h (e.injective ((degreeLTEquiv K 6).symm.injective eq)))
  · simp only [Fintype.card_prod, K, ZMod.card]
    have bound : p ≤ 10*b := by omega
    have hprod : p * (b * (p*p)) ≤ (10*b) * (b * ((10*b)*(10*b))) := by gcongr
    have hle := Nat.mul_le_mul_left p (Nat.sub_le (b*(p*p)) 1)
    have hstrong : p * (b * (p*p)) + 1 < b^6 := by
      have hh : 1001*b^4 < b^2*b^4 := Nat.mul_lt_mul_of_pos_right (by nlinarith [Nat.mul_le_mul hb hb]) (by positivity)
      have hb4 : 0 < b^4 := by positivity
      nlinarith only [hprod, hh, hb4]
    omega

end StrictLayerCode

/-! ## Encoding finset families as multiset families, and the closing theorem

Any family of `d`-subsets of a finite type `α` satisfying the set version of `(*)` is sent,
through `Fintype.equivFin α` and `Finset.val`, to an admissible family of size-`d` multisets
over `Fin (Fintype.card α)`.  A long such family therefore refutes `OMA.S_mo_40561.main`. -/

noncomputable section

namespace OMA.Disproof40561

open OMA.S_mo_40561

/-- Set version of admissibility for families of finsets of `α`. -/
def SetAdmissible {α : Type*} [DecidableEq α] (d t : ℕ) (F : Fin t → Finset (Finset α)) :
    Prop :=
  (∀ i, (F i).Nonempty) ∧ (∀ i, ∀ R ∈ F i, R.card = d) ∧
  (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
  ∀ i j k, i < j → j < k → ∀ R ∈ F i, ∀ T ∈ F k, ∃ S ∈ F j, R ∩ T ⊆ S

/-- The multiset encoding of a finset of `α`. -/
def enc {α : Type*} [Fintype α] (S : Finset α) : Multiset (Fin (Fintype.card α)) :=
  (S.map (Fintype.equivFin α).toEmbedding).val

theorem enc_injective {α : Type*} [Fintype α] : Function.Injective (enc (α := α)) := by
  intro S T h
  exact Finset.map_injective _ (Finset.val_injective h)

theorem enc_card {α : Type*} [Fintype α] (S : Finset α) :
    Multiset.card (enc S) = S.card := by
  simp only [enc, Finset.card_val, Finset.card_map]

theorem enc_inter {α : Type*} [Fintype α] [DecidableEq α] (S T : Finset α) :
    enc S ∩ enc T = enc (S ∩ T) := by
  simp only [enc, ← Finset.inter_val, Finset.map_inter]

theorem enc_le {α : Type*} [Fintype α] {S T : Finset α} : enc S ≤ enc T ↔ S ⊆ T := by
  simp only [enc, Finset.val_le_iff, Finset.map_subset_map]

/-- The encoded family. -/
def encode {α : Type*} [Fintype α] {t : ℕ} (F : Fin t → Finset (Finset α)) :
    Fin t → Finset (Multiset (Fin (Fintype.card α))) :=
  fun i => (F i).map ⟨enc, enc_injective⟩

theorem admissible_encode {α : Type*} [Fintype α] [DecidableEq α] {d t : ℕ}
    {F : Fin t → Finset (Finset α)} (hF : SetAdmissible d t F) :
    Admissible d (Fintype.card α) t (encode F) := by
  obtain ⟨hne, hcard, hdisj, hstar⟩ := hF
  refine ⟨fun i => (hne i).map, ?_, ?_, ?_⟩
  · intro i R hR
    obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hR
    rw [Function.Embedding.coeFn_mk, enc_card, hcard i S hS]
  · intro i j hij
    exact (Finset.disjoint_map _).mpr (hdisj i j hij)
  · intro i j k hij hjk R hR T hT
    obtain ⟨R', hR', rfl⟩ := Finset.mem_map.mp hR
    obtain ⟨T', hT', rfl⟩ := Finset.mem_map.mp hT
    obtain ⟨S, hS, hsub⟩ := hstar i j k hij hjk R' hR' T' hT'
    refine ⟨enc S, Finset.mem_map_of_mem _ hS, ?_⟩
    simp only [Function.Embedding.coeFn_mk]
    rw [enc_inter, enc_le]
    exact hsub

/-- Closing theorem: a set-admissible family longer than `d (|α| - 1) + 1` refutes `main`. -/
theorem not_main_of_family {α : Type*} [Fintype α] [DecidableEq α] {d t : ℕ}
    {F : Fin t → Finset (Finset α)} (hd : 1 ≤ d) (hα : 1 ≤ Fintype.card α)
    (hF : SetAdmissible d t F) (hlong : d * (Fintype.card α - 1) + 1 < t) :
    ¬ (type_of% @OMA.S_mo_40561.main) := by
  intro h
  have := (h d (Fintype.card α) hd hα).1 t (encode F) (admissible_encode hF)
  omega

end OMA.Disproof40561

end

open OAI.Geometry.Hirsch in
theorem OMA.Disproof40561.of_palette (h : Layer.PaletteTheorem) :
    ¬ (type_of% @OMA.S_mo_40561.main) := by
  obtain ⟨b,D,hb,ht,hp⟩ := h 6 (by decide) 1000
  obtain ⟨p⟩ := hp 1 (by decide)
  obtain ⟨α, inst, dec, W,d,hd,hr,hgap,hlong⟩ := StrictLayerCode.exists_words b ht
  obtain ⟨F,hne,hcard,hdisj,hmid⟩ := Layer.Palette.free_families (b^6) b D p W hd hr
    (by simpa [Nat.mul_comm] using hgap)
  have hs : 0 < b^6 := by positivity
  have hpos : 0 < Fintype.card α := lt_of_lt_of_le (by omega : 0 < d)
    ((hd ⟨0,hs⟩) ▸ Finset.card_le_univ (W ⟨0,hs⟩))
  apply not_main_of_family (d := d) (F := F) (by omega)
  · simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos (by omega) hpos
  · exact ⟨hne,hcard,hdisj,fun i j k hij hjk => hmid i j k hij.le hjk.le⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hlong

open OAI.Geometry.Hirsch in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_40561.main) :=
  OMA.Disproof40561.of_palette (Layer.palette_of_primary Layer.primary)

