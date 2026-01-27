import Mathlib.Data.Set.Card

import Mathlib.Tactic

open Set

section mathlib?

lemma n_exists (α : Type*) [Nonempty α] (r : α → T) :
    (∀ f g : α, r f = r g) ↔
    ∃ n, ∀ f : α, r f = n := by
  constructor <;> intro h
  · obtain ⟨f₀⟩ := ‹Nonempty α›
    use r f₀
    exact fun f => h f f₀
  · intro f g
    obtain ⟨n, hn⟩ := h
    rw [hn f, hn g]

lemma Nat.exists_between_of_lt_of_succ_ne {a b : ℕ} (hab : a < b) (hne : a + 1 ≠ b) :
    ∃ c, a < c ∧ c < b := by
  use a + 1
  exact ⟨Nat.lt_succ_self a, Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hab) hne⟩

lemma diff_encard_ne_top {f g : Set α} (hg : g.encard ≠ ⊤) (hs : f ⊂ g) :
    (g \ f).encard ≠ ⊤ := by
  intro h; apply hg
  rw [← encard_diff_add_encard_of_subset hs.subset, h, top_add]

lemma strict_intermediate [Preorder α] {f g : Set α} {b : α}
    (ha : f.encard.toNat + 2 ≤ g.encard.toNat)
    (hb : f ⊂ g)
    (nt : f.encard ≠ ⊤ ∧ g.encard ≠ ⊤) :
    ∃ c, c ∉ f ∧ c ∈ g ∧ c ≠ b := by
  -- g \ f has at least 2 elements
  have h_diff : 2 ≤ (g \ f).encard.toNat := by
    rw [← Set.encard_diff_add_encard_of_subset hb.subset,
      ENat.toNat_add (diff_encard_ne_top nt.2 hb) nt.1] at ha
    omega
  -- g \ f has at least 2 distinct elements
  have ⟨c, hc_mem, hc_ne_b⟩ : ∃ c, c ∈ g \ f ∧ c ≠ b := by
    by_cases h : b ∈ g \ f
    · convert Set.exists_ne_of_one_lt_ncard (Nat.lt_of_succ_le h_diff) b
    · obtain ⟨c, hc⟩ := nonempty_of_ssubset hb
      exact ⟨c, hc, fun hc_eq => h (hc_eq ▸ hc)⟩
  exact ⟨c, hc_mem.2, hc_mem.1, hc_ne_b⟩

lemma Pairwise.subset {α : Type*} {r : α → α → Prop} {s t : Set α}
    (h : s.Pairwise r) (hst : t ⊆ s) : t.Pairwise r :=
  fun _ hx _ hy hne => h (hst hx) (hst hy) hne

theorem Subtype.val_preimage_card (s t : Set α) (h : s ⊆ t) :
    (Subtype.val ⁻¹' s : Set t).encard = s.encard := by
  apply Set.encard_preimage_of_injective_subset_range
  exact Subtype.val_injective
  simp [h]

theorem Subtype.val_image_card (t : Set α) (s : Set t) :
    (Subtype.val '' s).encard = s.encard :=
  Function.Injective.encard_image Subtype.val_injective _

theorem Flag.map_carrier_encard {α : Type*} {β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) (f : Flag α) :
    (f.map e).carrier.encard = f.carrier.encard := by
  simpa [Flag.map, Equiv.coe_fn_mk] using ENat.card_image_of_injective _ _ e.injective

theorem IsChain.to_dual [LE α] (hs : @IsChain α (· ≤ ·) s) : @IsChain αᵒᵈ (· ≤ ·) s := by
  intro x hx y hy hne
  obtain h | h := hs hx hy hne
  · right; exact h
  · left; exact h

theorem IsChain.to_dual_iff [LE α] : @IsChain α (· ≤ ·) s ↔ @IsChain αᵒᵈ (· ≤ ·) s :=
  ⟨to_dual, to_dual⟩

theorem bijOn_encard_eq {α β : Type*} {f : α → β} {s : Set α} {t : Set β} (hf : Set.BijOn f s t) :
    s.encard.toNat = t.encard.toNat := by
  rw [Set.BijOn] at hf
  obtain ⟨hmaps, hinj, hsurj⟩ := hf
  have : s.encard = t.encard := by
    have := ENat.card_image_of_injOn hinj
    simp at this
    rw [← this]
    congr
    exact SurjOn.image_eq_of_mapsTo hsurj hmaps
  rw [this]

end mathlib?
