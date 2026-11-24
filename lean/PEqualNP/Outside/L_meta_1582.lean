import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1582

theorem main_aux : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  classical
  intro q m N L i0 T0 hq hm hmq _ hcard hmeet _ hT0 hT0c
  have few : ∀ t : Fin N, t ≠ i0 → (T0.filter (fun x => x ∈ L t)).card ≤ 1 := by
    intro t ht
    have hsub : T0.filter (fun x => x ∈ L t) ⊆ L t ∩ L i0 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      exact Finset.mem_inter.2 ⟨hv.2, hT0 hv.1⟩
    have := Finset.card_le_card hsub
    rw [hmeet t i0 ht] at this
    exact this
  have split : ∀ t : Fin N, (T0.filter (fun x => x ∈ L t)).card + (T0.filter (fun x => x ∉ L t)).card = m := by
    intro t
    rw [← hT0c]
    exact Finset.card_filter_add_card_filter_not (s := T0) (fun x => x ∈ L t)
  have many : ∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    intro t ht
    have h1 := few t ht
    have h2 := split t
    omega
  have off : ∀ t : Fin N, t ≠ i0 → ∃ v ∈ T0, v ∉ L t := by
    intro t ht
    have h1 := many t ht
    have hpos : 0 < (T0.filter (fun x => x ∉ L t)).card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter] at hv
    exact ⟨v, hv.1, hv.2⟩
  refine ⟨?_, ?_, many, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hall
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hall v hv))
  · intro t
    by_cases ht : t = i0
    · right
      intro v hv
      rw [ht]
      exact decide_eq_true hv
    · left
      obtain ⟨v, hv, hvt⟩ := off t ht
      exact ⟨v, hv, decide_eq_true hvt⟩
  · intro x hx
    exact Or.inl ⟨x, hx, decide_eq_true rfl⟩
  · right
    intro v hv
    exact decide_eq_true hv
  · intro r _
    right
    intro v hv
    exact decide_eq_true (Or.inl hv)
  · intro t
    constructor
    · apply decide_eq_false
      rintro ⟨v, hv, hd⟩
      exact (of_decide_eq_true hd) hv
    · intro p hp
      constructor
      · by_cases ht : t = i0
        · right
          intro v hv
          rw [ht]
          exact decide_eq_true (Or.inl hv)
        · left
          obtain ⟨v, hv, hvt⟩ := off t ht
          exact ⟨v, hv, decide_eq_true (Or.inl hvt)⟩
      · apply decide_eq_true
        exact ⟨p, hp, decide_eq_true (Or.inr rfl)⟩

end PEqualNP.Outside.L_meta_1582

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) :=
  PEqualNP.Outside.L_meta_1582.main_aux
