import Mathlib.Data.Set.Functor
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.Zorn

import Mathlib.Tactic

import AbstractPolytopes.Mathlib

open Set

section FlagOn

/-- The type of flags using only things in p. -/
structure FlagOn {α : Type*} [LE α] (p : Set α) where
  carrier : Set α
  carrier_sub : carrier ⊆ p
  Chain' : IsChain (· ≤ ·) carrier
  max_chain' : ∀ ⦃s⦄, s ⊆ p → IsChain (· ≤ ·) s → carrier ⊆ s → carrier = s

variable {α : Type*} [LE α] {s : Set α}

instance (s : Set α) : SetLike (FlagOn s) α := {
  coe f := f.carrier
  coe_injective' f g r := by cases f; cases g; congr
}

@[ext]
lemma FlagOn.ext {f g : FlagOn s} (h : f.carrier = g.carrier) :
  f = g := SetLike.ext' h

@[simp]
lemma coe_eq_carrierOn (hf : FlagOn s) : (↑hf : FlagOn s) = hf.carrier := rfl

@[simp]
lemma coe_eq_carrier (hf : Flag α) : (↑hf : Flag α) = hf.carrier := rfl

def liftFlag (f : FlagOn s) : Flag s :={
  carrier := Subtype.val⁻¹' f.carrier
  Chain' a ha b hb anb := by
    convert f.Chain' (mem_preimage.mp ha) (mem_preimage.mp hb) (Subtype.coe_ne_coe.mpr anb)
  max_chain' t tch chsub := by
    have := f.max_chain' (s := t) ?_ ?_ ?_
    · convert congr_arg (fun S => Subtype.val⁻¹' S) this
      simp
    · simp
    · intros x hx y hy hne
      exact tch (mem_of_mem_image_val hx) (mem_of_mem_image_val hy) (Subtype.coe_ne_coe.mp hne)
    · exact fun a ah => ⟨⟨a, f.carrier_sub ah⟩, chsub ah, rfl⟩
}

@[simp]
lemma liftcard (f : FlagOn s) : (liftFlag f).carrier.encard = f.carrier.encard :=
  Subtype.val_preimage_card f.carrier _ f.carrier_sub

def restrictFlag (f : Flag s) : FlagOn s :={
  carrier := f.carrier
  carrier_sub := Subtype.coe_image_subset s f.carrier
  Chain' a ha b hb anb := by
    convert f.Chain' (mem_of_mem_image_val ha) (mem_of_mem_image_val hb) (Subtype.coe_ne_coe.mp anb)
  max_chain' t tsub tch chsub := by
    have := f.max_chain' (s := Subtype.val ⁻¹' t) ?_ ?_
    · simpa [inter_eq_right.mpr tsub] using congr_arg (fun S => Subtype.val '' S) this
    · intros x hx y hy hne
      have hne' : (x : α) ≠ (y : α) := fun h => hne (Subtype.ext h)
      exact tch hx hy hne'
    · exact fun x hx => chsub ⟨x, hx, rfl⟩
}

@[simp]
lemma restrictcard (f : Flag s) : (restrictFlag f).carrier.encard = f.carrier.encard :=
  Subtype.val_image_card _ _

def sanity : FlagOn s ≃ Flag s where
  toFun := liftFlag
  invFun := restrictFlag
  left_inv f := by ext; simpa [restrictFlag, liftFlag] using fun hx => f.carrier_sub hx
  right_inv f := by ext; simp [restrictFlag, liftFlag]

section Preorder

variable {P : Type*} [Preorder P]

instance {s : Set P} : Inhabited (FlagOn s) :=
  ⟨restrictFlag (inferInstance : Nonempty (Flag s)).some⟩ -- urgh

-- TODO what why
noncomputable def someFlagOn (a : P) : FlagOn (Iic a) := default
noncomputable def someFlagOnIcc {a b : P} : FlagOn (Icc a b) := default

lemma Iic_bound_mem {a : P} (f : FlagOn (Iic a)) : a ∈ f.carrier := by
  rw [f.max_chain' (insert_subset (mem_Iic.2 le_rfl) f.carrier_sub)
    (f.Chain'.insert fun b hb hn => .inr <| mem_Iic.1 <| f.carrier_sub hb)
    (subset_insert _ _)]
  exact mem_insert _ _

lemma Icc_bounds_mem {a b : P} (hab : a ≤ b) (f : FlagOn (Icc a b)) :
  a ∈ f.carrier ∧ b ∈ f.carrier := by
  constructor
  · rw [f.max_chain' (insert_subset (mem_Icc.1 ⟨le_rfl, hab⟩) f.carrier_sub)
    (f.Chain'.insert fun c hc hn => .inl <| (mem_Icc.2 <| f.carrier_sub hc).1)
    (subset_insert _ _)]
    exact mem_insert _ _
  · rw [f.max_chain' (insert_subset (mem_Icc.2 ⟨hab, le_rfl⟩) f.carrier_sub)
    (f.Chain'.insert fun c hc hn => .inr <| (mem_Icc.1 <| f.carrier_sub hc).2)
    (subset_insert _ _)]
    exact mem_insert _ _

-- given a flag f on [⊥, a], we can find a global flag containing f and no other elemets of [⊥, a]
noncomputable def expandIic (a : P) (f : FlagOn (Iic a)) :
    ∃ fp : Flag P, f.carrier ⊆ fp.carrier ∧
    Disjoint (Iic a \ f.carrier) fp.carrier ∧
    ∀ x ∈ fp.carrier \ Iic a, ∀ y ∈ Iic a, y ≤ x := by
  -- there is a global flag that contains f
  obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
  have ch {x} (xs xz) := f.max_chain' (insert_subset xs f.carrier_sub) xz (subset_insert x _)
  refine ⟨z, orn, ?_, ?_⟩
  · by_contra h; simp [not_disjoint_iff, mem_diff] at h
    obtain ⟨x, ⟨xs, xf⟩, xz⟩ := h
    exact (insert_ne_self.mpr xf).symm
      <| ch xs (f.Chain'.insert (fun _ yf xn => z.Chain' xz (orn yf) xn))
  · simp only [mem_diff, mem_Iic, and_imp]
    have : a ∈ z.carrier := by
      refine orn ?_
      by_contra h
      refine h (insert_eq_self.mp ?_)
      exact (ch right_mem_Iic (f.Chain'.insert fun _ bf _ => .inr (f.carrier_sub bf))).symm
    intro b c d e ff
    rcases eq_or_ne b a with rfl | hne
    · exact ff
    · exact le_trans ff (z.Chain' c this |> fun h => by simp [d] at h; exact h hne)

noncomputable def expandIcc (α : Type*) [Preorder α] (a b : α) (alb : a ≤ b) (f : FlagOn (Icc a b)) :
    ∃ fp : Flag α, f.carrier ⊆ fp.carrier ∧
    Disjoint (Icc a b \ f.carrier) fp.carrier ∧
    ∀ x ∈ fp.carrier \ Icc a b, ∀ y ∈ Icc a b, x ≤ y ∨ y ≤ x := by
    obtain ⟨z,orn⟩ := IsChain.exists_subset_flag f.Chain'
    have ch {x} (xs xz) := f.max_chain' (insert_subset xs f.carrier_sub) xz (subset_insert x _)
    refine ⟨z, orn, ?_, ?_⟩
    · by_contra h; simp [not_disjoint_iff, mem_diff] at h
      obtain ⟨x, ⟨xs, xf⟩, xz⟩ := h
      exact (insert_ne_self.mpr xf).symm
        <| ch xs (f.Chain'.insert (fun _ yf xn => z.Chain' xz (orn yf) xn))
    · simp only [mem_diff, mem_Icc, not_and, and_imp]
      have hb : a ∈ z.carrier ∧ b ∈ z.carrier := by
        have hp := Icc_bounds_mem alb f
        exact ⟨orn hp.1, orn hp.2⟩
      intro x hx hneg y hy1 hy2
      by_cases hxa : a ≤ x
      · have := z.Chain' hx hb.2 (ne_of_not_le (hneg hxa))
        simp [hneg hxa] at this
        exact Or.inr <| le_trans hy2 this
      · have := z.Chain' hx hb.1 (ne_of_not_le hxa).symm
        simp [hxa] at this
        exact Or.inl <| le_trans this hy1

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

end Preorder

end FlagOn
