import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1633

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin h01 h0 h1 T hT t u ht hu htu
  have key : ∀ a : Fin N, a ≠ i0 → ¬ (p0 ∈ L a ∧ p1 ∈ L a) := by
    intro a ha hh
    have h := hint a i0 ha
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L a ∩ L i0 := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_inter]
      rcases hx with hx | hx
      · rw [hx]; exact ⟨hh.1, h0⟩
      · rw [hx]; exact ⟨hh.2, h1⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair h01, h] at h2
    omega
  have ex : ∀ a b : Fin N, a ≠ b → ∀ x : Fin N, ∃ p ∈ L a \ L b, p ≠ x := by
    intro a b hab x
    have h3 := Finset.card_sdiff_add_card_inter (L a) (L b)
    rw [hint a b hab, hcard a] at h3
    exact Finset.exists_mem_ne (by omega) x
  have kt := key t ht
  have ku := key u hu
  constructor
  · rintro ⟨⟨p, hp, v, hv, hTt⟩, ⟨p', hp', v', hv', hTu⟩⟩
    rw [hT] at hTt hTu
    rw [Finset.mem_sdiff] at hp hp'
    have A : (p0 ∉ L t ∧ p0 ∈ L u) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p1 ∈ L u) := by
      rcases hTt with h | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, _⟩
      · rw [h] at hv; exact absurd hv hp.2
      · rw [h] at hv; exact Or.inl ⟨a, hv⟩
      · rw [h] at hv; exact Or.inr ⟨a, b, hv⟩
      · exact absurd ⟨a, b⟩ kt
    have B : (p0 ∉ L u ∧ p0 ∈ L t) ∨ (p0 ∈ L u ∧ p1 ∉ L u ∧ p1 ∈ L t) := by
      rcases hTu with h | ⟨a, b, h⟩ | ⟨a, b, c, h⟩ | ⟨a, b, _⟩
      · rw [h] at hv'; exact absurd hv' hp'.2
      · rw [h] at hv'; exact Or.inl ⟨a, hv'⟩
      · rw [h] at hv'; exact Or.inr ⟨a, b, hv'⟩
      · exact absurd ⟨a, b⟩ ku
    rcases A with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩
    · rcases B with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · exact absurd b2 a1
      · exact Or.inr ⟨⟨b3, a1⟩, ⟨b1, b2⟩⟩
    · rcases B with ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
      · exact Or.inl ⟨⟨a1, a2⟩, ⟨a3, b1⟩⟩
      · exact absurd a3 b2
  · rintro (⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩)
    · obtain ⟨p, hp, hpn⟩ := ex t u htu p0
      obtain ⟨p', hp', hpn'⟩ := ex u t (Ne.symm htu) p1
      refine ⟨⟨p, hp, p1, c, ?_⟩, ⟨p', hp', p0, a, ?_⟩⟩
      · rw [hT]; exact Or.inr (Or.inr (Or.inl ⟨a, b, hpn, rfl⟩))
      · rw [hT]; exact Or.inr (Or.inl ⟨d, hpn', rfl⟩)
    · obtain ⟨p, hp, hpn⟩ := ex t u htu p1
      obtain ⟨p', hp', hpn'⟩ := ex u t (Ne.symm htu) p0
      refine ⟨⟨p, hp, p0, c, ?_⟩, ⟨p', hp', p1, a, ?_⟩⟩
      · rw [hT]; exact Or.inr (Or.inl ⟨b, hpn, rfl⟩)
      · rw [hT]; exact Or.inr (Or.inr (Or.inl ⟨c, d, hpn', rfl⟩))

end PEqualNP.Outside.L_meta_1633

theorem PEqualNP.Outside.L_meta_1633 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) :=
  PEqualNP.Outside.L_meta_1633.main_aux
