import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    (∀ x y : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) → (∀ v : Fin N, x v = true → y v = true) → (y p0 = true ∨ y p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → y u = true)) ∧
    (∀ t : Fin N, ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true)) ∧
    (∀ t : Fin N, ∀ p ∈ L t, (T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) := by
  classical
  intro q N L i0 p0 p1 _ _ _ hmeet _ h01 h0 h1 T hT
  have key : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t ht0 ht1
    by_contra hne
    have hc := hmeet t i0 hne
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
      intro v hv
      rw [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.2 ⟨ht0, h0⟩
      · exact Finset.mem_inter.2 ⟨ht1, h1⟩
    have h2 := Finset.card_le_card hsub
    rw [hc, Finset.card_pair h01] at h2
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with hx | hx | hx
    · exact Or.inl (hxy _ hx)
    · exact Or.inr (Or.inl (hxy _ hx))
    · exact Or.inr (Or.inr (fun u hu => hxy u (hx u hu)))
  · intro t
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · right
        right
        intro u hu
        have ht := key t ht0 ht1
        rw [ht]
        exact decide_eq_true hu
      · right
        left
        exact decide_eq_true ht1
    · left
      exact decide_eq_true ht0
  · intro t p _
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · by_cases hp0 : p = p0
        · left
          exact (hT t p p0).2 (Or.inl hp0.symm)
        · by_cases hp1 : p = p1
          · right
            left
            exact (hT t p p1).2 (Or.inl hp1.symm)
          · right
            right
            intro u hu
            have ht := key t ht0 ht1
            have hu2 : u ∉ L t := by
              rw [ht]
              exact hu
            exact (hT t p u).2 (Or.inr (Or.inr (Or.inr ⟨ht0, ht1, hp0, hp1, hu2⟩)))
      · by_cases hp0 : p = p0
        · left
          exact (hT t p p0).2 (Or.inl hp0.symm)
        · right
          left
          exact (hT t p p1).2 (Or.inr (Or.inr (Or.inl ⟨ht0, ht1, hp0, rfl⟩)))
    · by_cases hp1 : p = p1
      · right
        left
        exact (hT t p p1).2 (Or.inl hp1.symm)
      · left
        exact (hT t p p0).2 (Or.inr (Or.inl ⟨ht0, hp1, rfl⟩))
  · intro t
    constructor
    · apply decide_eq_false
      rintro ⟨v, hv, hd⟩
      exact (of_decide_eq_true hd) hv
    · intro p hp
      apply decide_eq_true
      exact ⟨p, hp, (hT t p p).2 (Or.inl rfl)⟩

end PEqualNP.Outside.L_meta_1630

theorem PEqualNP.Outside.L_meta_1630 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    (∀ x y : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) → (∀ v : Fin N, x v = true → y v = true) → (y p0 = true ∨ y p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → y u = true)) ∧
    (∀ t : Fin N, ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true)) ∧
    (∀ t : Fin N, ∀ p ∈ L t, (T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) :=
  PEqualNP.Outside.L_meta_1630.main_aux
