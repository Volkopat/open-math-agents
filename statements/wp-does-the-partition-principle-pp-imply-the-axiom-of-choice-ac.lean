import Mathlib

/-! Does PP imply AC over pure first-order ZF? The affirmative answer means ZF proves the implication, not that choice holds in the Lean metatheory.
Source: https://en.wikipedia.org/wiki/Axiom_of_choice#Possibly_equivalent_implications_of_AC (CC BY-SA 4.0)
Credit: @my-other-github-account (adaptation). Syntax, deduction and set-language definitions adapted from OpenAI, openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, ComparatorChallenges/PartitionConsistency.lean. Unused definitions omitted; target changed to the question of derivability.
-/
/-                                 Apache License
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
namespace OMA.S_wp_does_the_partition_principle_pp_imply_the_axiom_of_choice_ac

/-- Pure first-order membership syntax with equality. `n` variables are in scope.
A quantifier binds the last variable in its body. There are no atoms/urelements,
function symbols, constants, semantic predicates, or mathematical assumptions
in this syntax. -/
inductive Formula : ℕ → Type where
  | bot {n} : Formula n
  | mem {n} (x y : Fin n) : Formula n
  | equal {n} (x y : Fin n) : Formula n
  | imp {n} (p q : Formula n) : Formula n
  | conj {n} (p q : Formula n) : Formula n
  | disj {n} (p q : Formula n) : Formula n
  | all {n} (p : Formula (n + 1)) : Formula n
  | ex {n} (p : Formula (n + 1)) : Formula n

namespace Formula

abbrev neg {n} (p : Formula n) : Formula n := p.imp .bot
abbrev iff {n} (p q : Formula n) : Formula n := (p.imp q).conj (q.imp p)

/-- Under a binder, a renaming leaves the newly bound variable bound. -/
def liftRen {n m} (r : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (r i).castSucc)

/-- Capture-avoiding renaming; in this relational language all terms are variables. -/
def rename {n m} (r : Fin n → Fin m) : Formula n → Formula m
  | .bot => .bot
  | .mem x y => .mem (r x) (r y)
  | .equal x y => .equal (r x) (r y)
  | .imp p q => .imp (rename r p) (rename r q)
  | .conj p q => .conj (rename r p) (rename r q)
  | .disj p q => .disj (rename r p) (rename r q)
  | .all p => .all (rename (liftRen r) p)
  | .ex p => .ex (rename (liftRen r) p)

abbrev raise {n} (p : Formula n) : Formula (n + 1) := rename Fin.castSucc p

/-- Substitution of a variable term for the variable just quantified. -/
def instantiate {n} (p : Formula (n + 1)) (x : Fin n) : Formula n :=
  rename (Fin.lastCases x id) p

/-- Universal closure of all the free variables. -/
def close : {n : ℕ} → Formula n → Formula 0
  | 0, p => p
  | _ + 1, p => close (.all p)

end Formula

abbrev Sentence := Formula 0
abbrev Theory := Set Sentence

/-- Classical first-order natural deduction with equality. Hypotheses may be an
infinite theory, but a derivation is a finite inductive proof. The `allI` and
`exE` rules use a fresh last variable, and shift all assumptions to avoid
capture. We allow finitely many free variables in proofs of closed sentences. -/
inductive Derives : {n : ℕ} → Set (Formula n) → Formula n → Prop where
  | hyp {n} {Γ : Set (Formula n)} {p} : p ∈ Γ → Derives Γ p
  | weaken {n} {Γ Δ : Set (Formula n)} {p} :
      Γ ⊆ Δ → Derives Γ p → Derives Δ p
  | impI {n} {Γ : Set (Formula n)} {p q} :
      Derives (insert p Γ) q → Derives Γ (.imp p q)
  | impE {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.imp p q) → Derives Γ p → Derives Γ q
  | botE {n} {Γ : Set (Formula n)} {p} : Derives Γ .bot → Derives Γ p
  | classical {n} {Γ : Set (Formula n)} {p} :
      Derives (insert p.neg Γ) .bot → Derives Γ p
  | conjI {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ q → Derives Γ (.conj p q)
  | conjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ p
  | conjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ (.conj p q) → Derives Γ q
  | disjL {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ p → Derives Γ (.disj p q)
  | disjR {n} {Γ : Set (Formula n)} {p q} :
      Derives Γ q → Derives Γ (.disj p q)
  | disjE {n} {Γ : Set (Formula n)} {p q r} :
      Derives Γ (.disj p q) → Derives (insert p Γ) r →
      Derives (insert q Γ) r → Derives Γ r
  | allI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} :
      Derives (Formula.raise '' Γ) p → Derives Γ (.all p)
  | allE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (.all p) → Derives Γ (p.instantiate t)
  | exI {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} (t : Fin n) :
      Derives Γ (p.instantiate t) → Derives Γ (.ex p)
  | exE {n} {Γ : Set (Formula n)} {p : Formula (n + 1)} {q : Formula n} :
      Derives Γ (.ex p) → Derives (insert p (Formula.raise '' Γ)) q.raise →
      Derives Γ q
  | eqRefl {n} {Γ : Set (Formula n)} (t : Fin n) : Derives Γ (.equal t t)
  | eqSubst {n} {Γ : Set (Formula n)} {s t : Fin n} (p : Formula (n + 1)) :
      Derives Γ (.equal s t) → Derives Γ (p.instantiate s) →
      Derives Γ (p.instantiate t)
  | rename {n m} {Γ : Set (Formula n)} {p : Formula n} (r : Fin n → Fin m) :
      Derives Γ p → Derives (Formula.rename r '' Γ) (Formula.rename r p)

namespace SetLanguage
open Formula

/-! All abbreviations in this namespace expand to formulas of the pure language
of equality and membership. Functions are sets of Kuratowski pairs *inside the
structure*. In particular, no quantification over external Lean functions is
used in PP, Choice, or ordinal-indexed Choice. -/

/-- `a ⊆ b`. -/
def subset {n} (a b : Fin n) : Formula n :=
  rename ![a, b] (Formula.all ((Formula.mem 2 0).imp (Formula.mem 2 1)) : Formula 2)

/-- `a = ∅`. -/
def empty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.all (Formula.mem 1 0).neg : Formula 1)

/-- `a ≠ ∅`, stated as existence of a member. -/
def nonempty {n} (a : Fin n) : Formula n :=
  rename ![a] (Formula.ex (Formula.mem 1 0) : Formula 1)

/-- `p = {x,y}`. -/
def unorderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.all ((Formula.mem 3 0).iff ((Formula.equal 3 1).disj (Formula.equal 3 2))) : Formula 3)

/-- `b = a ∪ {a}`. -/
def successor {n} (b a : Fin n) : Formula n :=
  rename ![b, a]
    (Formula.all ((Formula.mem 2 0).iff ((Formula.mem 2 1).disj (Formula.equal 2 1))) : Formula 2)

/-- Kuratowski ordered pair: `p = {{x},{x,y}}`. -/
def orderedPair {n} (p x y : Fin n) : Formula n :=
  rename ![p, x, y]
    (Formula.ex (Formula.ex ((unorderedPair 3 1 1).conj
      ((unorderedPair 4 1 2).conj (unorderedPair 0 3 4)))) : Formula 3)

/-- The internal graph relation `⟨x,y⟩ ∈ f`. -/
def edge {n} (f x y : Fin n) : Formula n :=
  rename ![f, x, y]
    (Formula.ex ((Formula.mem 3 0).conj (orderedPair 3 1 2)) : Formula 3)

/-- `f` is a set graph of a function whose domain is exactly `d`.
The first conjunct excludes non-pairs and graph entries outside the domain;
the second conjunct asserts totality and single-valuedness. -/
def functionOn {n} (f d : Fin n) : Formula n :=
  rename ![f, d]
    ((Formula.all ((Formula.mem 2 0).imp
        (Formula.ex (Formula.ex ((Formula.mem 3 1).conj (orderedPair 2 3 4)))))).conj
      (Formula.all ((Formula.mem 2 1).imp
        (Formula.ex ((edge 0 2 3).conj (Formula.all ((edge 0 2 4).imp (Formula.equal 4 3))))))) : Formula 2)

/-- Internal set function `f : d → r`. -/
def mapsTo {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((functionOn 0 1).conj
      (Formula.all (Formula.all ((Formula.mem 3 1).imp ((edge 0 3 4).imp (Formula.mem 4 2))))) : Formula 3)

/-- Internal set surjection `f : d ↠ r`. -/
def surjection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all ((Formula.mem 3 2).imp (Formula.ex ((Formula.mem 4 1).conj (edge 0 4 3))))) : Formula 3)

/-- Internal set injection `f : d ↪ r`. -/
def injection {n} (f d r : Fin n) : Formula n :=
  rename ![f, d, r]
    ((mapsTo 0 1 2).conj
      (Formula.all (Formula.all (.all
        ((Formula.mem 3 1).imp ((Formula.mem 4 1).imp
          (((edge 0 3 5).conj (edge 0 4 5)).imp (Formula.equal 3 4))))))) : Formula 3)

/-- Transitivity of a set (not transitivity of the external structure). -/
def transitiveSet {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 1).imp (Formula.mem 2 0)))) : Formula 1)

/-- Membership is an internal strict linear order on `a`. -/
def membershipLinear {n} (a : Fin n) : Formula n :=
  rename ![a]
    ((Formula.all ((Formula.mem 1 0).imp (Formula.mem 1 1).neg)).conj
      ((Formula.all (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp ((Formula.mem 3 0).imp
        (((Formula.mem 1 2).conj (Formula.mem 2 3)).imp (Formula.mem 1 3)))))))).conj
        (Formula.all (Formula.all ((Formula.mem 1 0).imp ((Formula.mem 2 0).imp
          ((Formula.equal 1 2).disj ((Formula.mem 1 2).disj (Formula.mem 2 1)))))))) : Formula 1)

/-- Every nonempty internal subset of `a` has a membership-minimal element.
This does NOT assert external well-foundedness of the relation. -/
def membershipWellFounded {n} (a : Fin n) : Formula n :=
  rename ![a]
    (Formula.all (((subset 1 0).conj (nonempty 1)).imp
      (Formula.ex ((Formula.mem 2 1).conj (Formula.all ((Formula.mem 3 1).imp (Formula.mem 3 2).neg))))) : Formula 1)

/-- A choice function on the set `A` of nonempty sets. -/
def choiceOn {n} (c A : Fin n) : Formula n :=
  rename ![c, A]
    ((functionOn 0 1).conj
      (Formula.all ((Formula.mem 2 1).imp (Formula.ex ((edge 0 2 3).conj (Formula.mem 3 2))))) : Formula 2)

/-- The Partition Principle. The reverse injection is not required to be a
section of the original surjection. Both `X` and `Y` range over all sets. -/
def PP : Sentence :=
  Formula.all (Formula.all ((Formula.ex (surjection 2 0 1)).imp (Formula.ex (injection 2 1 0))))

/-- Ordinary Choice for every set of nonempty sets. -/
def AC : Sentence :=
  Formula.all ((Formula.all ((Formula.mem 1 0).imp (nonempty 1))).imp (Formula.ex (choiceOn 1 0)))

/-! Full pure-set ZF, not a finite fragment and not ZFA. -/

def extensionality : Sentence :=
  Formula.all (Formula.all ((Formula.all ((Formula.mem 2 0).iff (Formula.mem 2 1))).imp (Formula.equal 0 1)))

def emptySet : Sentence := Formula.ex (empty 0)

def pairing : Sentence := Formula.all (Formula.all (Formula.ex (unorderedPair 2 0 1)))

def union : Sentence :=
  Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (Formula.ex ((Formula.mem 3 0).conj (Formula.mem 2 3))))))

def powerSet : Sentence := Formula.all (Formula.ex (Formula.all ((Formula.mem 2 1).iff (subset 2 0))))

def infinity : Sentence :=
  Formula.ex ((Formula.ex ((Formula.mem 1 0).conj (empty 1))).conj
    (Formula.all ((Formula.mem 1 0).imp (Formula.ex ((Formula.mem 2 0).conj (successor 2 1))))))

def foundation : Sentence :=
  Formula.all ((nonempty 0).imp
    (Formula.ex ((Formula.mem 1 0).conj (Formula.all ((Formula.mem 2 1).imp (Formula.mem 2 0).neg)))))

/-- The instance of Separation for an entirely arbitrary formula `p(params,x)`.
All parameters are universally closed. Neither the quantifier complexity of
`p` nor the number of parameters is bounded. -/
def separation {n} (p : Formula (n + 1)) : Sentence :=
  let A : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let B : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let x : Fin (n + 3) := Fin.last (n + 2)
  let r : Fin (n + 1) → Fin (n + 3) :=
    Fin.lastCases x (fun i => i.castSucc.castSucc.castSucc)
  close (Formula.all (Formula.ex (Formula.all ((Formula.mem x B).iff ((Formula.mem x A).conj (rename r p))))))

/-- Substitution into a binary formula with `n` additional parameters. -/
def relation {n m} (p : Formula (n + 2)) (params : Fin n → Fin m) (x y : Fin m) :
    Formula m :=
  rename (Fin.lastCases y (Fin.lastCases x params)) p

/-- The instance of Replacement for an entirely arbitrary formula
`p(params,x,y)`: if it is single-valued and total on `A`, its image is a set.
As with Separation, the parameters are all universally closed. -/
def replacement {n} (p : Formula (n + 2)) : Sentence :=
  let unique : Formula (n + 3) :=
    Formula.all ((relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last (n + 1)).castSucc.castSucc (Fin.last (n + 3))).imp
      (Formula.equal (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc))
  let totalFunctional : Formula (n + 1) :=
    Formula.all ((Formula.mem (Fin.last (n + 1)) (Fin.last n).castSucc).imp
      (Formula.ex ((relation p (fun i => i.castSucc.castSucc.castSucc)
        (Fin.last (n + 1)).castSucc (Fin.last (n + 2))).conj unique)))
  let image : Formula (n + 1) :=
    Formula.ex (Formula.all ((Formula.mem (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc).iff
      (Formula.ex ((Formula.mem (Fin.last (n + 3)) (Fin.last n).castSucc.castSucc.castSucc).conj
        (relation p (fun i => i.castSucc.castSucc.castSucc.castSucc)
          (Fin.last (n + 3)) (Fin.last (n + 2)).castSucc)))))
  close (Formula.all (totalFunctional.imp image))

/-- Exactly the axioms and all schema instances of pure first-order ZF. -/
inductive IsZFAxiom : Sentence → Prop where
  | extensionality : IsZFAxiom extensionality
  | emptySet : IsZFAxiom emptySet
  | pairing : IsZFAxiom pairing
  | union : IsZFAxiom union
  | powerSet : IsZFAxiom powerSet
  | infinity : IsZFAxiom infinity
  | foundation : IsZFAxiom foundation
  | separation {n} (p : Formula (n + 1)) : IsZFAxiom (separation p)
  | replacement {n} (p : Formula (n + 2)) : IsZFAxiom (replacement p)

/-- Zermelo–Fraenkel set theory, without Choice. -/
def ZF : Theory := {p | IsZFAxiom p}

end SetLanguage

theorem main : Derives SetLanguage.ZF (SetLanguage.PP.imp SetLanguage.AC) := by
  sorry

end OMA.S_wp_does_the_partition_principle_pp_imply_the_axiom_of_choice_ac
