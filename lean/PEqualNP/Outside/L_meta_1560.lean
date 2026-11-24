import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1560

def Ln (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

theorem Ln_self (t : Fin 21) : t ∈ Ln t := by simp [Ln]

theorem Ln_card : ∀ t : Fin 21, (Ln t).card = 5 := by decide +kernel

theorem Ln_ne : ∀ t t' : Fin 21, t ≠ t' → ∃ v, v ∈ Ln t ∧ v ∉ Ln t' := by decide +kernel

theorem Ln_sep : ∀ a s : Fin 21, a ≠ s → ∃ t, s ∈ Ln t ∧ a ∉ Ln t := by decide +kernel

theorem comp_big (t : Fin 21) (S : Finset (Fin 21)) (hS : S.card ≤ 2) :
    ∃ v, v ∉ Ln t ∧ v ∉ S := by
  by_contra h
  push Not at h
  have hsub : (Ln t)ᶜ ⊆ S := fun v hv => h v (Finset.mem_compl.1 hv)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_compl, Ln_card] at hc
  simp at hc
  omega

theorem part1 (M T : Finset (Fin 21)) (hex : ∃ v ∈ T, v ∉ M)
    (f : (Fin 21 → Bool) → Bool)
    (hmono : ∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) :
    ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ M, x v = true)) ↔
          ((∀ a ∈ T ∩ M, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ M, ∀ s ∈ M \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ M)) = false)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_inter] at ha
      rw [h _ ⟨a, ha.1, by simp⟩]
      exact decide_eq_true ⟨a, ha.2, by simp⟩
    · intro a ha s hs
      rw [Finset.mem_sdiff] at ha hs
      rw [h _ ⟨a, ha.1, by simp⟩]
      exact decide_eq_true ⟨s, hs.1, by simp⟩
    · obtain ⟨v, hvT, hvM⟩ := hex
      rw [h _ ⟨v, hvT, by simpa using hvM⟩]
      apply decide_eq_false
      rintro ⟨w, hw, hw2⟩
      simp at hw2
      exact hw2 hw
  · rintro ⟨ha, hb, hc⟩ x ⟨v0, hv0T, hv0⟩
    by_cases hx : ∃ v ∈ M, x v = true
    · rw [decide_eq_true hx]
      obtain ⟨v, hvM, hv⟩ := hx
      by_cases hvT : v ∈ T
      · apply hmono _ _ _ (ha v (Finset.mem_inter.2 ⟨hvT, hvM⟩))
        intro w hw
        have hwv : w = v := by simpa using hw
        rw [hwv]; exact hv
      · by_cases hv0M : v0 ∈ M
        · apply hmono _ _ _ (ha v0 (Finset.mem_inter.2 ⟨hv0T, hv0M⟩))
          intro w hw
          have hwv : w = v0 := by simpa using hw
          rw [hwv]; exact hv0
        · apply hmono _ _ _ (hb v0 (Finset.mem_sdiff.2 ⟨hv0T, hv0M⟩) v (Finset.mem_sdiff.2 ⟨hvM, hvT⟩))
          intro w hw
          have hwv : w = v0 ∨ w = v := by simpa using hw
          rcases hwv with h | h
          · rw [h]; exact hv0
          · rw [h]; exact hv
    · rw [decide_eq_false hx]
      by_contra hfx
      have hfx' : f x = true := by simpa using hfx
      have hle : ∀ w : Fin 21, x w = true → (fun v : Fin 21 => decide (v ∉ M)) w = true := by
        intro w hw
        apply decide_eq_true
        intro hwM
        exact hx ⟨w, hwM, hw⟩
      have hbad := hmono x (fun v : Fin 21 => decide (v ∉ M)) hle hfx'
      rw [hc] at hbad
      exact Bool.false_ne_true hbad

def iA (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  T.image (fun a => fun v : Fin 21 => decide (v = a))

def iB (T : Finset (Fin 21)) : Finset (Fin 21 → Bool) :=
  (T ×ˢ Tᶜ).image (fun p => fun v : Fin 21 => decide (v = p.1 ∨ v = p.2))

def iC : Finset (Fin 21 → Bool) :=
  Finset.univ.image (fun t => fun v : Fin 21 => decide (v ∉ Ln t))

theorem memA (T : Finset (Fin 21)) (x : Fin 21 → Bool) :
    x ∈ iA T ↔ ∃ t : Fin 21, ∃ a ∈ T ∩ Ln t, x = (fun v : Fin 21 => decide (v = a)) := by
  unfold iA
  rw [Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, a, Finset.mem_inter.2 ⟨ha, Ln_self a⟩, rfl⟩
  · rintro ⟨t, a, ha, rfl⟩
    exact ⟨a, (Finset.mem_inter.1 ha).1, rfl⟩

theorem memB (T : Finset (Fin 21)) (x : Fin 21 → Bool) :
    x ∈ iB T ↔ ∃ t : Fin 21, ∃ a ∈ T \ Ln t, ∃ s ∈ Ln t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)) := by
  unfold iB
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, s⟩, hp, rfl⟩
    rw [Finset.mem_product, Finset.mem_compl] at hp
    have hne : a ≠ s := fun h => hp.2 (by rw [← h]; exact hp.1)
    obtain ⟨t, hs, ha⟩ := Ln_sep a s hne
    exact ⟨t, a, Finset.mem_sdiff.2 ⟨hp.1, ha⟩, s, Finset.mem_sdiff.2 ⟨hs, hp.2⟩, rfl⟩
  · rintro ⟨t, a, ha, s, hs, rfl⟩
    exact ⟨(a, s), Finset.mem_product.2 ⟨(Finset.mem_sdiff.1 ha).1,
      Finset.mem_compl.2 (Finset.mem_sdiff.1 hs).2⟩, rfl⟩

theorem memC (x : Fin 21 → Bool) :
    x ∈ iC ↔ ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ Ln t)) := by
  unfold iC
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, Finset.mem_univ _, rfl⟩

theorem cardA (T : Finset (Fin 21)) (hT : T.card = 3) : (iA T).card = 3 := by
  unfold iA
  have hinj : Function.Injective (fun a : Fin 21 => fun v : Fin 21 => decide (v = a)) := by
    intro a b h
    have h1 := congrFun h a
    simpa using h1
  rw [Finset.card_image_of_injective _ hinj, hT]

theorem cardB (T : Finset (Fin 21)) (hT : T.card = 3) : (iB T).card = 54 := by
  unfold iB
  have hinj : Set.InjOn (fun p : Fin 21 × Fin 21 => fun v : Fin 21 => decide (v = p.1 ∨ v = p.2))
      (↑(T ×ˢ Tᶜ) : Set (Fin 21 × Fin 21)) := by
    rintro ⟨a, s⟩ hp ⟨a', s'⟩ hp' h
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_compl] at hp hp'
    have h1 := congrFun h a
    have h2 := congrFun h s
    simp at h1 h2
    have ea : a = a' := by
      rcases h1 with h | h
      · exact h
      · exact absurd (by rw [← h]; exact hp.1) hp'.2
    have es : s = s' := by
      rcases h2 with h | h
      · exact absurd (by rw [h]; exact hp'.1) hp.2
      · exact h
    rw [ea, es]
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_compl, hT]
  simp

theorem cardC : iC.card = 21 := by
  unfold iC
  have hinj : Function.Injective (fun t : Fin 21 => fun v : Fin 21 => decide (v ∉ Ln t)) := by
    intro t t' h
    by_contra hne
    obtain ⟨v, hv, hv'⟩ := Ln_ne t t' hne
    have h1 := congrFun h v
    simp [hv, hv'] at h1
  rw [Finset.card_image_of_injective _ hinj]
  simp

theorem disjAB (T : Finset (Fin 21)) : Disjoint (iA T) (iB T) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  unfold iA at hxA
  unfold iB at hxB
  rw [Finset.mem_image] at hxA hxB
  obtain ⟨a, ha, rfl⟩ := hxA
  obtain ⟨⟨b, s⟩, hp, h⟩ := hxB
  rw [Finset.mem_product, Finset.mem_compl] at hp
  have h1 := congrFun h b
  have h2 := congrFun h s
  simp at h1 h2
  exact hp.2 (by rw [h2, ← h1]; exact hp.1)

theorem disjAC (T : Finset (Fin 21)) : Disjoint (iA T) iC := by
  rw [Finset.disjoint_left]
  intro x hxA hxC
  unfold iA at hxA
  unfold iC at hxC
  rw [Finset.mem_image] at hxA hxC
  obtain ⟨a, ha, rfl⟩ := hxA
  obtain ⟨t, -, h⟩ := hxC
  obtain ⟨v, hv, hva⟩ := comp_big t {a} (by simp)
  rw [Finset.mem_singleton] at hva
  have h1 := congrFun h v
  simp [hv, hva] at h1

theorem disjBC (T : Finset (Fin 21)) : Disjoint (iB T) iC := by
  rw [Finset.disjoint_left]
  intro x hxB hxC
  unfold iB at hxB
  unfold iC at hxC
  rw [Finset.mem_image] at hxB hxC
  obtain ⟨⟨b, s⟩, hp, rfl⟩ := hxB
  obtain ⟨t, -, h⟩ := hxC
  obtain ⟨v, hv, hvS⟩ := comp_big t {b, s} Finset.card_le_two
  rw [Finset.mem_insert, Finset.mem_singleton] at hvS
  have h1 := congrFun h v
  simp [hv, hvS] at h1

theorem cardU (T : Finset (Fin 21)) (hT : T.card = 3) : (iA T ∪ iB T ∪ iC).card = 78 := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨disjAC T, disjBC T⟩),
    Finset.card_union_of_disjoint (disjAB T), cardA T hT, cardB T hT, cardC]

theorem main_aux : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ T : Finset (Fin 21), T.card = 3 → (∀ t : Fin 21, ¬ T ⊆ L t) →
    (∀ f : (Fin 21 → Bool) → Bool,
      (∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) →
      ∀ t : Fin 21,
        ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
          ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L t)) = false))) ∧
    (∀ t : Fin 21, ∃ v ∈ T, v ∉ L t) ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 := by
  intro L hL T hT hnl
  obtain rfl : L = Ln := funext hL
  have h2 : ∀ t : Fin 21, ∃ v ∈ T, v ∉ Ln t := fun t => Finset.not_subset.1 (hnl t)
  refine ⟨fun f hmono t => part1 (Ln t) T (h2 t) f hmono, h2, ?_, ?_, ?_, ?_⟩
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans (cardA T hT)
    rw [memA, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans (cardB T hT)
    rw [memB, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans cardC
    rw [memC, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  · refine (congrArg Finset.card (Finset.ext fun x => ?_)).trans (cardU T hT)
    rw [Finset.mem_union, Finset.mem_union, memA, memB, memC, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, h | h | h⟩
      · exact Or.inl (Or.inl ⟨t, h⟩)
      · exact Or.inl (Or.inr ⟨t, h⟩)
      · exact Or.inr ⟨t, h⟩
    · rintro ((⟨t, h⟩ | ⟨t, h⟩) | ⟨t, h⟩)
      · exact ⟨t, Or.inl h⟩
      · exact ⟨t, Or.inr (Or.inl h)⟩
      · exact ⟨t, Or.inr (Or.inr h)⟩

end PEqualNP.Outside.L_meta_1560

theorem PEqualNP.Outside.L_meta_1560 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ T : Finset (Fin 21), T.card = 3 → (∀ t : Fin 21, ¬ T ⊆ L t) →
    (∀ f : (Fin 21 → Bool) → Bool,
      (∀ x y : Fin 21 → Bool, (∀ v : Fin 21, x v = true → y v = true) → f x = true → f y = true) →
      ∀ t : Fin 21,
        ((∀ x : Fin 21 → Bool, (∃ v ∈ T, x v = true) → f x = decide (∃ v ∈ L t, x v = true)) ↔
          ((∀ a ∈ T ∩ L t, f (fun v : Fin 21 => decide (v = a)) = true) ∧
           (∀ a ∈ T \ L t, ∀ s ∈ L t \ T, f (fun v : Fin 21 => decide (v = a ∨ v = s)) = true) ∧
           f (fun v : Fin 21 => decide (v ∉ L t)) = false))) ∧
    (∀ t : Fin 21, ∃ v ∈ T, v ∉ L t) ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a)))).card = 3 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, ∃ a ∈ T \ L t, ∃ s ∈ L t \ T,
      x = (fun v : Fin 21 => decide (v = a ∨ v = s)))).card = 54 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 21 ∧
    (Finset.univ.filter (fun x : Fin 21 → Bool => ∃ t : Fin 21, (∃ a ∈ T ∩ L t, x = (fun v : Fin 21 => decide (v = a))) ∨
      (∃ a ∈ T \ L t, ∃ s ∈ L t \ T, x = (fun v : Fin 21 => decide (v = a ∨ v = s))) ∨
      x = (fun v : Fin 21 => decide (v ∉ L t)))).card = 78 :=
  PEqualNP.Outside.L_meta_1560.main_aux
