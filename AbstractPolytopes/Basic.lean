import Mathlib.Order.Grade
import Mathlib.Order.SuccPred.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse

import AbstractPolytopes.FlagOn

import Mathlib.Tactic

open Set

---- stuff to ask ----
-- - it is so incredibly annoying to work with encard is there relief?
-- - defining the rank by using whatever some flag feels odd. is it ok?
-- - it is the correct thing to do to define induced rank and use that to define abstract p., yeah?
-- - so when should i use subtypes and when should i use sets idk

section pureFlag

def PureFlag (α : Type*) [LE α] := ∃ n : ℕ, ∀ f : Flag α, f.carrier.encard = n

@[simp]
lemma finite_of_pureFlag [LE α] (h : PureFlag α) (f : Flag α) : f.carrier.Finite :=
  finite_of_encard_eq_coe (h.choose_spec f)

variable {P : Type*} [Preorder P] {a b : P} {s t : Set P}

lemma finiteOn_of_pureFlag (h : PureFlag P) (f : FlagOn s) : f.carrier.Finite := by
  obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
  exact (finite_of_encard_eq_coe (h.choose_spec z)).subset orn

lemma pureFlag_ne_top (h : PureFlag P) (f : FlagOn s) : f.carrier.encard ≠ ⊤ :=
  (finiteOn_of_pureFlag h f).encard_lt_top.ne

lemma flag_encardtoNat_eq_of_pureFlag (h : PureFlag P) (f g : Flag P) :
    f.carrier.encard.toNat = g.carrier.encard.toNat := by
  repeat rw [h.choose_spec]

-- TODO this is the most annoyin thing ever what
lemma card_eq_of_pureFlagd (h : PureFlag P) (f : FlagOn s) :
    ↑f.carrier.encard.toNat = f.carrier.encard  := by
  obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
  exact ((finite_of_encard_eq_coe (h.choose_spec z)).subset orn).encard_eq_coe.symm

open Set FlagOn in
theorem flagOn_encard_eq_of_pureFlag_subset (h : PureFlag P) (alb : a ≤ b) (f g : FlagOn (Icc a b)) :
    f.carrier.encard = g.carrier.encard := by
  by_contra hc
  wlog hl : (f.carrier.encard) < g.carrier.encard
  · simp only [not_lt, le_iff_eq_or_lt] at hl
    exact match hl with | .inl e => hc e.symm | .inr e => this h alb g f (ne_of_lt e) e
  · -- make f into a proper flag
    let ⟨m, hm⟩ := h
    obtain ⟨fp, dd, sas, sus⟩ := expandIcc P a b alb f
    -- take the chain that is g together with whatever was added to f to make fp
    set dif := fp.carrier \ f.carrier
    let cc : IsChain (· ≤ ·) (g ∪ dif) := by
      apply isChain_union.mpr ⟨g.Chain', ⟨fp.Chain'.diff, ?_⟩⟩
      simp only [mem_diff, ne_eq, and_imp]
      intros x xg y yfp ynf xny
      refine (sus y (mem_diff_of_mem yfp ?_) x (g.carrier_sub xg)).symm
      by_contra cc
      exact sas.notMem_of_mem_right yfp ⟨cc, ynf⟩

    -- there is a flag that contains this chain
    obtain ⟨hg, gle⟩ := cc.exists_subset_flag
    have nmn := encard_mono gle
    simp only [coe_eq_carrierOn, coe_eq_carrier] at nmn
    rw [(finite_of_pureFlag h hg).encard_eq_coe, hm hg] at nmn

    -- but it must be bigger than the flag we got by extending f because f < g
    refine (ne_of_lt (lt_of_lt_of_le ?_ nmn)) (hm fp)
    have difd : Disjoint g.carrier (fp.carrier \ f.carrier) := by
      rw [Set.disjoint_iff]
      intro x ⟨hxg, hxdiff⟩
      exact Set.disjoint_iff.mp sas ⟨⟨g.carrier_sub hxg, hxdiff.2⟩, hxdiff.1⟩
    have := encard_diff_add_encard fp.carrier f.carrier
    rw [union_eq_self_of_subset_right dd] at this
    -- this is outrageous
    rw [encard_union_eq difd, ← this, add_comm]
    rw [← card_eq_of_pureFlagd h f, ← card_eq_of_pureFlagd h g, (finite_of_pureFlag h fp).diff.encard_eq_coe]
    norm_cast
    gcongr
    -- this is also outrageous
    rw [← card_eq_of_pureFlagd h f, ← card_eq_of_pureFlagd h g] at hl
    norm_cast at hl


-- nice theorem: if all flags on P have the same size, so do all flags that only use stuff up to a
open Set FlagOn in
theorem flagOn_encard_eq_of_pureFlag (h : PureFlag P) (f g : FlagOn (Iic a)) :
    f.carrier.encard = g.carrier.encard := by
  by_contra hc
  wlog hl : (f.carrier.encard) < g.carrier.encard
  · simp only [not_lt, le_iff_eq_or_lt] at hl
    exact match hl with | .inl e => hc e.symm | .inr e => this h g f (ne_of_lt e) e

  · -- make f into a proper flag
    let ⟨m, hm⟩ := h
    obtain ⟨hf, dd, sas, sus⟩ := expandIic a f

    -- take the chain that is g together with whatever was added to f to make hf
    set dif := hf.carrier \ f.carrier
    let cc : IsChain (· ≤ ·) (g ∪ dif) := by
      apply isChain_union.mpr ⟨g.Chain', _⟩
      refine ⟨hf.Chain'.diff, fun aa ag b bd anb => .inl (sus _ ?_ _ (g.carrier_sub ag))⟩
      simp only [mem_diff, mem_of_mem_inter_left bd, mem_Iic, true_and]
      by_contra
      have := mem_diff_of_mem (mem_Iic.mpr this) (notMem_of_mem_diff bd)
      exact sas.notMem_of_mem_left this (diff_subset bd)

    -- there is a flag that contains this chain
    obtain ⟨hg, gle⟩ := cc.exists_subset_flag
    have nmn := encard_mono gle
    simp only [coe_eq_carrierOn, coe_eq_carrier] at nmn
    rw [(finite_of_pureFlag h hg).encard_eq_coe, hm hg] at nmn

    -- but it must be bigger than the flag we got by extending f because f < g
    refine (ne_of_lt (lt_of_lt_of_le ?_ nmn)) (hm hf)
    have difd : Disjoint g.carrier (hf.carrier \ f.carrier) := by
      rw [Set.disjoint_iff]
      intro x ⟨hxg, hxdiff⟩
      exact Set.disjoint_iff.mp sas ⟨⟨g.carrier_sub hxg, hxdiff.2⟩, hxdiff.1⟩
    have := encard_diff_add_encard hf.carrier f.carrier
    rw [union_eq_self_of_subset_right dd] at this
    -- this is outrageous
    rw [encard_union_eq difd, ← this, add_comm]
    rw [← card_eq_of_pureFlagd h f, ← card_eq_of_pureFlagd h g, (finite_of_pureFlag h hf).diff.encard_eq_coe]
    norm_cast
    gcongr
    -- this is also outrageous
    rw [← card_eq_of_pureFlagd h f, ← card_eq_of_pureFlagd h g] at hl
    norm_cast at hl

lemma flagOn_encardtoNat_eq_of_pureFlag (h : PureFlag P) (f g : FlagOn (Iic a)) :
    f.carrier.encard.toNat = g.carrier.encard.toNat :=
  congrArg ENat.toNat (flagOn_encard_eq_of_pureFlag h f g)

lemma rankex (h : PureFlag P) (a : P) : ∃ n, ∀ f : FlagOn (Iic a), f.carrier.encard = n :=
  (n_exists _ _).mp (flagOn_encard_eq_of_pureFlag h)

-- the order is mono
-- this is an iff actually
lemma flagOn_card_mono (h : PureFlag P) {a b : P} (alb : a < b) (f : FlagOn (Iic a)) (g : FlagOn (Iic b)) :
    f.carrier.encard.toNat < g.carrier.encard.toNat := by
  let f' := extendFlag alb.le f
  have : f.carrier.encard.toNat < f'.carrier.encard.toNat := by
    rw [← ENat.coe_lt_coe, card_eq_of_pureFlagd h f', card_eq_of_pureFlagd h f]
    exact Set.Finite.encard_lt_encard (finiteOn_of_pureFlag h f) <| extendFlag_carrier_lt alb f
  rwa [flagOn_encard_eq_of_pureFlag h f' g] at this


lemma iicPure (h : PureFlag P) (a : P) : PureFlag (Iic a) := by
  use (someFlagOn a).carrier.encard.toNat
  rw [card_eq_of_pureFlagd h]
  simpa [restrictcard] using fun f => flagOn_encard_eq_of_pureFlag h (restrictFlag f) (someFlagOn a)

lemma dualPure (h : PureFlag P) : PureFlag Pᵒᵈ := by
  use h.choose
  intro f
  exact h.choose_spec ⟨f.carrier, f.Chain'.to_dual, fun _ hc hs => f.max_chain' hc.to_dual hs⟩

def subtypeOrderIso (t : Set α) [Preorder α] :
    t ≃o {x : α | x ∈ t} := by
  refine ⟨⟨id, fun x => ⟨x.val, x.property⟩, ?_, ?_⟩, ?_⟩
  · intro; rfl
  · intro; rfl
  · intros; rfl

lemma interPure {s t : Set P} (ha : PureFlag s) (hb : PureFlag t) :
    PureFlag (Set.inter s t) := by
  use ha.choose ⊓ hb.choose
  intro factor_orderIso_map_one_eq_bot
    -- have a := ha.pure ⟨Subtype.map _ inter_subset_left '' f.carrier, ?_, fun _ hc hs => ?_⟩
    -- have b := hb.pure ⟨Subtype.map _ inter_subset_right '' f.carrier, ?_, fun _ hc hs => ?_⟩
    -- simp [Subtype.val_image_card] at a b
    -- sorry
    -- sorry
    -- sorry
  sorry

lemma iccPure {a b : P} (alb : a ≤ b) (h : PureFlag P) : PureFlag (Icc a b) := by
  have hb : PureFlag (Iic b) := sorry
  have ha : PureFlag (Iic a) := sorry
  have := (dualPure ha)
  sorry







end pureFlag

-- -- main result: there is a rank implied by pureFlag and SectionChainConnected
-- noncomputable instance inducedGrading {P : Type*} [PartialOrder P] [BoundedOrder P]
--     [h : PureFlag P] :
--     GradeOrder ℤ P := {
--   grade a := ((someFlagOn a).carrier.encard.toNat : ℤ) - 1
--   grade_strictMono a b alb := by
--     simpa using flagOn_card_mono alb (someFlagOn a) (someFlagOn b)
--   covBy_grade a b alb := by
--       set f := someFlagOn a
--       set g := extendFlag alb.le f
--       have card_lt := flagOn_card_mono alb.1 f g

--       simp only [CovBy, sub_lt_sub_iff_right, Nat.cast_lt, not_lt, tsub_le_iff_right] at alb ⊢
--       rw [flagOn_encardtoNat_eq_of_pureFlag _ g]
--       refine ⟨flagOn_card_mono alb.1 f g, fun m hm => ?_⟩
--       have sub : f.carrier ⊂ g.carrier := extendFlag_carrier_lt alb.1 f
--       have : g.carrier.encard.toNat = f.carrier.encard.toNat + 1 := by
--         by_contra hhc

--         have : f.carrier.encard.toNat + 2 ≤ g.carrier.encard.toNat := by omega
--         obtain ⟨c, h, hh, hhh⟩ :=
--           strict_intermediate this sub ⟨pureFlag_ne_top f, pureFlag_ne_top g⟩

--         have cnmem : c ∉ Iic a := fun cmem => Set.ne_insert_of_notMem _ h <|
--           f.max_chain' (insert_subset cmem f.carrier_sub)
--             (Set.pairwise_insert.mpr ⟨f.Chain', fun b bm bnc => by convert g.Chain' hh (sub.le bm) bnc; simpa using Or.symm⟩)
--             (subset_insert c f.carrier)
--         have anc := (ne_of_mem_of_not_mem (f.carrier_sub (Iic_bound_mem f)) cnmem)

--         have alt : a < c := by cases g.Chain' (sub.le (Iic_bound_mem f)) hh anc with
--         | inl h => exact lt_of_le_not_ge h cnmem
--         | inr h => exact absurd cnmem (by simpa)

--         have ltb : c < b := by cases g.Chain' (Iic_bound_mem g) hh hhh.symm with
--         | inl h => exact absurd (g.carrier_sub hh) (fun hc => hhh (le_antisymm hc h))
--         | inr h => exact lt_of_le_of_ne (by simp at h; convert h) hhh

--         exact alb.2 alt ltb
--       simp [this, Int.le_of_sub_one_lt hm]
-- }


-- main result: there is a rank implied by pureFlag and SectionChainConnected
noncomputable instance PureFlag.inducedGrading {P : Type*} [PartialOrder P] [BoundedOrder P]
    (h : PureFlag P) :
    GradeOrder ℕ P := {
  grade a := (someFlagOn a).carrier.encard.toNat
  grade_strictMono a b alb := by
    simpa using flagOn_card_mono h alb (someFlagOn a) (someFlagOn b)
  covBy_grade a b alb := by
      set f := someFlagOn a
      set g := extendFlag alb.le f
      simp [flagOn_encardtoNat_eq_of_pureFlag h _ g, ← Order.succ_eq_iff_covBy]

      by_contra hhc

      have card_lt := flagOn_card_mono h alb.1 f g
      have sub : f.carrier ⊂ g.carrier := extendFlag_carrier_lt alb.1 f
      have : f.carrier.encard.toNat + 2 ≤ g.carrier.encard.toNat := by omega

      obtain ⟨c, h, hh, hhh⟩ :=
        strict_intermediate this sub ⟨pureFlag_ne_top h f, pureFlag_ne_top h g⟩

      have cnmem : c ∉ Iic a := fun cmem => Set.ne_insert_of_notMem _ h <|
        f.max_chain' (insert_subset cmem f.carrier_sub)
          (Set.pairwise_insert.mpr ⟨f.Chain', fun b bm bnc => by convert g.Chain' hh (sub.le bm) bnc; simpa using Or.symm⟩)
          (subset_insert c f.carrier)

      have anc := (ne_of_mem_of_not_mem (f.carrier_sub (Iic_bound_mem f)) cnmem)
      have alt : a < c := by cases g.Chain' (sub.le (Iic_bound_mem f)) hh anc with
      | inl h => exact lt_of_le_not_ge h cnmem
      | inr h => exact absurd cnmem (by simpa)

      have ltb : c < b := by cases g.Chain' (Iic_bound_mem g) hh hhh.symm with
      | inl h => exact absurd (g.carrier_sub hh) (fun hc => hhh (le_antisymm hc h))
      | inr h => exact lt_of_le_of_ne (by simp at h; convert h) hhh

      exact alb.2 alt ltb
}

-- for sanity
lemma top_grade_eq_n {P : Type*} [PartialOrder P] [BoundedOrder P] (h : PureFlag P) :
    h.inducedGrading.grade (⊤ : P) = h.choose := by
  simp [GradeOrder.grade, ← liftcard]
  rw [← (ENat.toNat_coe (h.choose))]
  rw [← h.choose_spec ((liftFlag (someFlagOn (⊤ : P))).map OrderIso.IicTop), Flag.map_carrier_encard]

lemma bot_grade_eq_one {P : Type*} [PartialOrder P] [BoundedOrder P] (h : PureFlag P) :
    h.inducedGrading.grade (⊥ : P) = 1 := by
  simp [GradeOrder.grade, ← liftcard, liftFlag]
  rw [Subtype.val_preimage_card _ _ (someFlagOn ⊥).carrier_sub]
  set dd : FlagOn (Iic (⊥ : P)) := {
    carrier := {⊥}
    carrier_sub a b := by simp_all
    Chain' := by exact IsChain.singleton
    max_chain' a b c d := by
      ext; constructor <;> intros <;> simp_all
  }
  have := flagOn_encardtoNat_eq_of_pureFlag h dd (someFlagOn ⊥)
  simp only [(by unfold dd; simp : dd.carrier.encard = 1)] at this
  convert this.symm
  simp [ENat.toNat_eq_iff_eq_coe, Nat.cast_one]

def IsProper [LE α] [BoundedOrder α] (s : α) : Prop := s ≠ ⊤ ∧ s ≠ ⊤

-- A bounded pure poset P of rank n is called connected if either n ≤ 1, or n ≥ 2 and for
-- any two proper faces F and G of P there exists a finite sequence of proper faces
-- F = H0, H1, . . . , Hk−1, Hk = G of P such that Hi−1 and Hi are incident for i = 1, . . . , k.
def ChainConnected (P : Type*) [PartialOrder P] [BoundedOrder P] (h : PureFlag P) :=
    h.inducedGrading.grade (⊤ : P) ≤ 1 ∨
    ∀ {f g : {p | IsProper p}}, ((SimpleGraph.hasse P).induce {p | IsProper p}).Reachable f g

-- all right so i use subtype here maybe i shouldnt?
def SectionChainConnected (P : Type*) [PartialOrder P] [BoundedOrder P] (h : PureFlag P) :=
  ∀ {a b : P}, [alb : Fact (a ≤ b)] → ChainConnected (Icc a b) (iccPure alb.elim h)

/- An abstract polytope a partial order that is bounded, graded, section-connected, and satisfies
the diamond property, that is, if the grades of two elements a < b differ by 2, then there are
exactly 2 elements that lie strictly between a and b. -/
class AbstractPolytope (P : Type*) extends PartialOrder P, BoundedOrder P where
  pure : PureFlag P
  connected : SectionChainConnected P pure
  diamond : ∀ {a b : P}, a ≤ b →
      pure.inducedGrading.grade a + (2 : ℤ) = pure.inducedGrading.grade b →
      {x | a < x ∧ x < b}.ncard = 2

-- instance : AbstractPolytope Pᵒᵖ := sorry

-- instance {a b : P} : AbstractPolytope (Icc a b) := sorry
