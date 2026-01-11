import Mathlib.Order.Grade

import AbstractPolytopes.FlagOn

import Mathlib.Tactic

open Set

---- stuff to ask ----
-- - it is so incredibly annoying to work with encard is there relief?
-- - defining the rank by using whatever some flag feels odd. is it ok?
-- - it is the correct thing to do to define induced rank and use that to define abstract p., yeah?

section pureFlag

def pureFlag (α : Type*) [LE α] := ∃ n : ℕ, ∀ f : Flag α, f.carrier.encard = n

@[simp]
lemma finite_of_pureFlag [LE α] (h : pureFlag α) (f : Flag α) : f.carrier.Finite :=
  finite_of_encard_eq_coe (h.choose_spec f)

variable {P : Type*} [Preorder P] {a b : P} {s t : Set P}

lemma finiteOn_of_pureFlag (h : pureFlag P) (f : FlagOn s) : f.carrier.Finite := by
  obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
  exact (finite_of_encard_eq_coe (h.choose_spec z)).subset orn

lemma pureFlag_ne_top (h : pureFlag P) (f : FlagOn s) : f.carrier.encard ≠ ⊤ :=
  (finiteOn_of_pureFlag h f).encard_lt_top.ne

-- TODO this is the most annoyin thing ever what
lemma card_eq_of_pureFlagd (h : pureFlag P) (f : FlagOn s) :
    ↑f.carrier.encard.toNat = f.carrier.encard  := by
  obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
  exact ((finite_of_encard_eq_coe (h.choose_spec z)).subset orn).encard_eq_coe.symm

-- nice theorem: if all flags on P have the same size, so do all flags that only use stuff up to a
open Set FlagOn in
theorem flagOn_encard_eq_of_pureFlag (h : pureFlag P) (f g : FlagOn (Iic a)) :
    f.carrier.encard = g.carrier.encard := by
  by_contra hc
  wlog hl : (f.carrier.encard) < g.carrier.encard
  · simp only [not_lt, le_iff_eq_or_lt] at hl
    exact match hl with | .inl e => hc e.symm | .inr e => this h g f (ne_of_lt e) e

  · -- make f into a proper flag
    let ⟨m, hm⟩ := h
    obtain ⟨hf, dd, sas, sus⟩ := expandIcc P a f

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

lemma flagOn_encardtoNat_eq_of_pureFlag (h : pureFlag P) (f g : FlagOn (Iic a)) :
    f.carrier.encard.toNat = g.carrier.encard.toNat :=
  congrArg ENat.toNat (flagOn_encard_eq_of_pureFlag h f g)

lemma rankex {a : P} (h : pureFlag P) : ∃ n, ∀ f : FlagOn (Iic a), f.carrier.encard = n :=
  (n_exists _ _).mp (flagOn_encard_eq_of_pureFlag h)


/-- Extend a given flag on `Iic a` to a flag on `Iic b` thatn contains it. -/
def extendFlag {a b : P} (hab : a ≤ b) (f : FlagOn (Iic a)) :
      FlagOn (Iic b) where
    carrier := f.carrier ∪ (default : FlagOn (Icc a b)).carrier
    carrier_sub := by
      rintro x (hf | hg)
      · exact le_trans (f.carrier_sub hf) hab
      · exact ((default : FlagOn (Icc a b)).carrier_sub hg).2
    Chain' := by
      set f' : FlagOn (Icc a b) := default
      rintro x (hxf | hxg) y (hyf | hyg) hne
      · exact f.Chain' hxf hyf hne
      · left; exact le_trans (f.carrier_sub hxf) (f'.carrier_sub hyg).1
      · right; exact le_trans (f.carrier_sub hyf) (f'.carrier_sub hxg).1
      · exact f'.Chain' hxg hyg hne
    max_chain' := by
      intro s hs hchain hcarrier_sub
      ext z; refine ⟨fun hz => hcarrier_sub hz, fun hz => ?_⟩
      by_cases hne : z = a
      · rw [hne]; exact Or.inl (Iic_bound_mem _)
      · rcases hchain hz (hcarrier_sub (Or.inr (Icc_bounds_mem hab _).1)) hne with hza | haz
        · left
          exact (f.max_chain' (Set.inter_subset_right)
            (fun _ hx _ hy => hchain hx.1 hy.1)
            (fun _ hw => ⟨hcarrier_sub (Or.inl hw), f.carrier_sub hw⟩)).symm ▸ ⟨hz, hza⟩
        · right
          set f' : FlagOn (Icc a b) := default
          exact (f'.max_chain' (Set.inter_subset_right)
            (fun _ hx _ hy => hchain hx.1 hy.1)
            (fun _ hw => ⟨hcarrier_sub (Or.inr hw), f'.carrier_sub hw⟩)).symm ▸
            ⟨hz, haz, hs hz⟩

-- extendFlag in fact extends the flag
lemma extendFlag_carrier_lt {a b : P} (hab : a < b) (f : FlagOn (Iic a)) :
  f.carrier ⊂ (extendFlag hab.le f).carrier := by
  simp only [extendFlag, ssubset_union_left_iff]
  exact fun c => hab.not_ge <| f.carrier_sub <| c (Icc_bounds_mem hab.le _).2

-- the order is mono
-- this is an iff actually
lemma flagOn_card_mono {a b : P} (h : pureFlag P) (alb : a < b)
    (f : FlagOn (Iic a)) (g : FlagOn (Iic b)) :
    f.carrier.encard.toNat < g.carrier.encard.toNat := by
  let f' := extendFlag alb.le f
  have : f.carrier.encard.toNat < f'.carrier.encard.toNat := by
    rw [← ENat.coe_lt_coe, card_eq_of_pureFlagd h f', card_eq_of_pureFlagd h f]
    exact Set.Finite.encard_lt_encard (finiteOn_of_pureFlag h f) <| extendFlag_carrier_lt alb f
  rwa [flagOn_encard_eq_of_pureFlag h f' g] at this

-- TODO would be nice to have that sections are pure if the whole thing is
theorem sectionPure (h : pureFlag P) : pureFlag ↑(Icc a b) := sorry

end pureFlag


-- main result: there is a rank implied by pureFlag and SectionChainConnected
noncomputable instance inducedGrading {P : Type*} [PartialOrder P] [BoundedOrder P]
    (h : pureFlag P) :
    GradeOrder ℤ P := {
  grade a := ((someFlagOn a).carrier.encard.toNat : ℤ) - 1
  grade_strictMono a b alb := by
    simpa using flagOn_card_mono h alb (someFlagOn a) (someFlagOn b)
  covBy_grade a b alb := by
      set f := someFlagOn a
      set g := extendFlag alb.le f
      have card_lt := flagOn_card_mono h alb.1 f g

      simp only [CovBy, sub_lt_sub_iff_right, Nat.cast_lt, not_lt, tsub_le_iff_right] at alb ⊢
      rw [flagOn_encardtoNat_eq_of_pureFlag h _ g]
      refine ⟨flagOn_card_mono h alb.1 f g, fun m hm => ?_⟩
      have sub : f.carrier ⊂ g.carrier := extendFlag_carrier_lt alb.1 f
      have : g.carrier.encard.toNat = f.carrier.encard.toNat + 1 := by
        by_contra hhc

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
      simp [this, Int.le_of_sub_one_lt hm]
}

def IsProper [LE α] [BoundedOrder α] (s : α) : Prop := ⊤ ≠ s ∧ ⊥ ≠ s

-- A bounded pure poset P of rank n is called connected if either n ≤ 1, or n ≥ 2 and for
-- any two proper faces F and G of P there exists a finite sequence of proper faces
-- F = H0, H1, . . . , Hk−1, Hk = G of P such that Hi−1 and Hi are incident for i = 1, . . . , k.
def ChainConnected (P : Type*) [PartialOrder P] [BoundedOrder P] (h : pureFlag P) :=
    (inducedGrading h).grade ⊤ ≤ 1 ∨
    ∀ {f g : P}, ∃ s : Set P, s.Finite ∧ (∀ t ∈ s, IsProper t) ∧ IsChain (· ⋖ ·) s ∧ f ∈ s ∧ g ∈ s

-- all right so i use subtype here maybe i shouldnt?
def SectionChainConnected (P : Type*) [PartialOrder P] [BoundedOrder P] (h : pureFlag P) :=
  ∀ {a b : P}, [Fact (a ≤ b)] → ChainConnected (Icc a b) (sectionPure h)

/- An abstract polytope a partial order that is bounded, graded, section-connected, and satisfies
the diamond property, that is, if the grades of two elements a < b differ by 2, then there are
exactly 2 elements that lie strictly between a and b. -/
class AbstractPolytope (P : Type*) extends PartialOrder P, BoundedOrder P where
  pure : pureFlag P
  connected : SectionChainConnected P pure
  diamond : ∀ {a b : P}, a ≤ b →
      (inducedGrading pure).grade a + (2 : ℤ) = (inducedGrading pure).grade b →
      {x | a < x ∧ x < b}.ncard = 2

-- instance : AbstractPolytope Pᵒᵖ := sorry

-- instance {a b : P} : AbstractPolytope (Icc a b) := sorry
