import Mathlib.Order.Grade
import Mathlib.Order.SuccPred.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Basic
import Mathlib.Order.Atoms
import Mathlib.Data.Finset.Sort




open Set




section Definitions

/-- An abstract pre-polytope is a bounded graded poset that satisfies the diamond property. -/
def IsAbstractPrePolytope (P : Type*) [PartialOrder P] [BoundedOrder P] [g : GradeOrder ℕ P] :=
  ∀ (x y : P), g.grade y = g.grade x + 2 → (Ioo x y).encard = 2


section ChainConnectedPrereqs

variable {α : Type*} [Preorder α]

/-- The order embedding from a subtype of α into α. -/
def subO (p : α → Prop) : Subtype p ↪o α :=
  ⟨⟨Subtype.val, Subtype.coe_injective⟩, by simp⟩

-- a graded order on α induces a graded order on the closed interval [a, b]
instance IccGrade [go : GradeOrder ℕ α] {a b : α} :
    GradeOrder ℕ (Set.Icc a b) where
  grade x := grade ℕ x.val
  grade_strictMono _ _ xly := grade_strictMono xly
  covBy_grade x y c := by
    have := c.image (subO _) (by simpa [subO] using Set.ordConnected_Icc)
    convert go.covBy_grade this

/-- An element of a bounded order is called proper if it is neither the top nor the bottom element. -/
def IsProper [BoundedOrder α] (s : α) : Prop := s ≠ ⊤ ∧ s ≠ ⊤

end ChainConnectedPrereqs

variable (P : Type*) [PartialOrder P] [BoundedOrder P] [g : GradeOrder ℕ P]

-- A bounded pure poset P of rank n is called connected if either n ≤ 1, or n ≥ 2 and for
-- any two proper faces F and G of P there exists a finite sequence of proper faces
-- F = H0, H1, . . . , Hk−1, Hk = G of P such that Hi−1 and Hi are incident for i = 1, . . . , k.
def ChainConnected :=
    g.grade (⊤ : P) ≤ 1 ∨
    ∀ {f g : {p | IsProper p}}, ((SimpleGraph.hasse P).induce {p | IsProper p}).Reachable f g

-- all right so i use subtype here maybe i shouldnt?
def SectionChainConnected := ∀ {a b : P}, [Fact (a ≤ b)] → ChainConnected (Icc a b)

/-- An abstract polytope is a bounded graded poset that satisfies the diamond property and is
strongly connected. -/
def IsAbstractPolytope (P : Type*) [PartialOrder P] [BoundedOrder P] [g : GradeOrder ℕ P] :=
  IsAbstractPrePolytope P ∧ SectionChainConnected P

end Definitions


section FlagPurity

variable {P : Type*} [PartialOrder P] [BoundedOrder P] [g : GradeOrder ℕ P]

-- GOAL: in an abstract pre-polytope, all flags have the same size.
-- alternatively, we can prove that every flag has size g.grade ⊤ + 1
-- this is called Jordan-Dedekind chain condition sometimes
theorem IsAbstractPrePolytope.flagCardEq (ap : IsAbstractPrePolytope P) (f f' : Flag P) :
    f.carrier.encard.toNat = f'.carrier.encard.toNat := sorry

-- probably makes sense to check out what's in
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Grade.html

-- proof idea 1: induction on the size of the lattice g.grade ⊤. a flag F in P must contain an
-- element c that covers ⊤ (this is called Coatomic in mathlib and i think its not proven there for
-- flags). if we remove ⊤ from F we get a flag F' in the interval [⊥, c], which is also an abstract
-- pre-polytope (see IsAbstractPrePolytope.Icc). by inductive hypothesis, F' has length g.grade c
-- which is g.grade ⊤ - 1
-- note that this is tricky, because if we view the interval [⊥, c] as a type, we need to prove
-- that it is actually "smaller" than P so the induction terminates...not sure how to do that kinda
-- thing

-- proof idea 2: prove that every flag can be sorted s.t. each element covers the next.
-- we have cov_grade_succ (h : x ⋖ y) : g.grade x + 1 = g.grade y. ⊤ is contained in every flag,
-- so its the last thing in that sorted flag, so grade ⊤ + 1 is the length of the flag

-- here's some stuff that could be useful:

-- the open interval (x, y) : Set [a, b] is equivalent to the open interval (x, y) : Set P
-- this is a bit odd and probably not what i should do
def IooSubtypeEquiv{α : Type*} [Preorder α] {a b : α} (x y : ↑(Icc a b)) : Ioo x y ≃ Ioo x.val y.val := by
  refine ⟨fun z => ⟨z.val.val, z.prop⟩, fun z => ⟨⟨z.val, ?_⟩, z.prop⟩, fun z => rfl, fun z => rfl⟩
  refine mem_Icc.mp ⟨?_, ?_⟩
  exact (lt_of_le_of_lt (mem_Icc.mp x.prop).1 (mem_Ioo.mp z.prop).1).le
  exact (lt_of_lt_of_le (mem_Ioo.mp z.prop).2 (mem_Icc.mp y.prop).2).le

/-- The induced order on every closed interval of an abstract pre-polytope is itself an abstract
pre-polytope. -/
theorem IsAbstractPrePolytope.Icc (ap : IsAbstractPrePolytope P) {a b : P}
    [Fact (a ≤ b)] : IsAbstractPrePolytope (Icc a b) := by
  intro x y hg
  have : g.grade y.val = g.grade x.val + 2 :=
    ((fun {a b} ↦ Nat.succ_inj.mp) (congrArg Nat.succ hg.symm)).symm
  convert ap x y this
  exact Set.encard_congr (IooSubtypeEquiv x y)

-- another nice goal
-- instance {a b : P}  [Fact (a ≤ b)] : IsAbstractPolytope (Icc a b) := sorry

omit [BoundedOrder P] in
theorem grade_injective_le {a b : P} (hab : a ≤ b) (h_grade : g.grade a = g.grade b) :
    a = b := by
  cases eq_or_lt_of_le hab with
  | inl h => exact h
  | inr h => exact ((g.grade_strictMono h).ne h_grade).elim

-- the grade is injective on chains (and hence, flags)
omit [BoundedOrder P] in
theorem grade_InjOn_IsChain (s : Set P) (hs : IsChain (· ≤ ·) s) :
    Set.InjOn g.grade s := by
  intro a ha b hb h_grade
  cases hs.total ha hb with
  | inl hab => exact grade_injective_le hab h_grade
  | inr hba => exact (grade_injective_le hba h_grade.symm).symm

lemma grade_le_top (a : P) : g.grade a ≤ g.grade (⊤ : P) := by
  by_cases ha : a ≠ ⊤
  · exact (g.grade_strictMono ha.symm.lt_top').le
  · simp at ha; rw [ha]

-- in bounded graded orders all chains are finite
-- this will let us convert flag carriers to finset
theorem chain_finite {s : Set P} (hs : IsChain (· ≤ ·) s) :
    s.Finite := by
  have h_image : g.grade '' s ⊆ Finset.range (g.grade (⊤ : P) + 1) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := hn
    simpa using Nat.lt_succ_of_le (grade_le_top a)
  have := Set.Finite.subset (Finset.finite_toSet _) h_image
  exact Set.Finite.of_finite_image this (grade_InjOn_IsChain s hs)

-- a graded bounded order induces a linear order on its flags
noncomputable instance (f : Flag P) : LinearOrder f where
  le_total a b := f.Chain'.total a.prop b.prop
  toDecidableLE := Classical.decRel LE.le

-- at most one element per grade in a chain
omit [BoundedOrder P] in
lemma unique_grade_in_chain (s : Set P) (f : IsChain (· ≤ ·) s) (hx : x ∈ s) (hy : y ∈ s)
    (hg : g.grade x = g.grade y) :
    x = y := by
  obtain (h | h) := f.total hx hy
  · by_contra hne
    have : x < y := h.lt_of_ne hne
    have : g.grade x < g.grade y := grade_strictMono this
    omega
  · by_contra hne
    push_neg at hne
    have : y < x := h.lt_of_ne hne.symm
    have : g.grade y < g.grade x := grade_strictMono this
    omega

-- in an ℕ-graded order, if x covers y the grades are one apart
omit [BoundedOrder P] in
lemma cov_grade_succ (h : x ⋖ y) : g.grade x + 1 = g.grade y :=
  Order.covBy_iff_add_one_eq.mp <| g.covBy_grade h

-- any preorder on the nonempty closed interval is bounded
instance IccBounded {α : Type*} [Preorder α] {a b : α} [h : Fact (a ≤ b)] :
    BoundedOrder (Set.Icc a b) where
  top := ⟨b, right_mem_Icc.mpr h.elim⟩
  le_top x := (mem_Icc.mp x.prop).2
  bot := ⟨a, left_mem_Icc.mpr h.elim⟩
  bot_le x := (mem_Icc.mp x.prop).1

end FlagPurity


-- i played with the induction idea a bit but some of those sorries are juicy
theorem flagPure_of_apo (P : Type*) (po : PartialOrder P) (bo : BoundedOrder P) (g : GradeOrder ℕ P)
   (ap : IsAbstractPrePolytope P) (f : Flag P) :
    f.carrier.encard.toNat = g.grade ⊤ + 1 := by
  cases h : g.grade ⊤ + 1 with
  | zero => simp at h
  | succ n =>
      rw [← h]
      -- this needs proving and is not easy
      obtain ⟨c, coc⟩ : ∃ c, c ∈ f ∧ IsCoatom c := sorry
      have : Fact (⊥ ≤ c) := Fact.mk (OrderBot.bot_le c)
      have := ap.Icc (a := (⊥ : P)) (b := c)
      -- the flag with ⊤ removed
      let f' : Flag (Icc ⊥ c) := {
        carrier := {x | x.val ∈ f.carrier}
        Chain' x hx y hy xny := f.Chain' hx hy (Subtype.coe_ne_coe.mpr xny)
        max_chain' z ch h := by
          sorry -- this should follow directly from f.max_chain'
      }
      -- inductive hypothesis
      have ih := flagPure_of_apo (Icc ⊥ c) _ IccBounded IccGrade this f'
      -- now some annoying stuff needs to happen to talk about sizes of sets under subtype coercion:
      have eep : (IccGrade.grade (⊤ : Icc ⊥ c)) + 1 = g.grade ⊤ := sorry -- this needs the coatom (coc)
      have : f.carrier.encard = f'.carrier.encard + 1 := by simp [f']; sorry
      rw [← eep, this, ← ih]
      -- some annoying stuff about encard and sets that we know are finite urgh
      sorry
termination_by f.carrier.encard
decreasing_by sorry -- we have to prove termination here :D because how should lean know f' is smaller than f
