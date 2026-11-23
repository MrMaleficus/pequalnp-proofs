import Mathlib
import PEqualNP.Defs

/-!
# Nine rectangles for the triangle with three pendant edges

Each cell (edge, independent set) lies in one rectangle, and the vertex of that rectangle is an
end of the edge outside the set. Four independent sets suffice: `{0,4,5}`, `{1,3,5}`, `{2,3,4}`
and `{3,4,5}`. Each pendant vertex has a cell that forces a rectangle of its own. Each triangle
vertex has three forced cells; if they share one rectangle, its cross cells split the forced
cells of the other two triangle vertices into two and three rectangles. So the triangle
vertices need six rectangles in every case.
-/

namespace PEqualNP.Outside.L_meta_462_aux

/-- The triangle `0 1 2` with the pendant edges `0 3`, `1 4`, `2 5`. -/
abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun a b : Fin 6 =>
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
  (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))

/-- A cell: an edge and an independent set. -/
def Ok (e : Sym2 (Fin 6)) (I : Finset (Fin 6)) : Prop :=
  e ∈ G.edgeSet ∧ ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w

abbrev e01 : Sym2 (Fin 6) := s(0, 1)
abbrev e02 : Sym2 (Fin 6) := s(0, 2)
abbrev e12 : Sym2 (Fin 6) := s(1, 2)
abbrev e03 : Sym2 (Fin 6) := s(0, 3)
abbrev e14 : Sym2 (Fin 6) := s(1, 4)
abbrev e25 : Sym2 (Fin 6) := s(2, 5)
abbrev I1 : Finset (Fin 6) := {0, 4, 5}
abbrev I2 : Finset (Fin 6) := {1, 3, 5}
abbrev I3 : Finset (Fin 6) := {2, 3, 4}
abbrev I4 : Finset (Fin 6) := {3, 4, 5}

lemma he01 : e01 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma he02 : e02 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma he12 : e12 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma he03 : e03 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma he14 : e14 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma he25 : e25 ∈ G.edgeSet := by rw [SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]; decide
lemma hI1 : ∀ u ∈ I1, ∀ w ∈ I1, ¬ G.Adj u w := by simp only [SimpleGraph.fromRel_adj]; decide
lemma hI2 : ∀ u ∈ I2, ∀ w ∈ I2, ¬ G.Adj u w := by simp only [SimpleGraph.fromRel_adj]; decide
lemma hI3 : ∀ u ∈ I3, ∀ w ∈ I3, ¬ G.Adj u w := by simp only [SimpleGraph.fromRel_adj]; decide
lemma hI4 : ∀ u ∈ I4, ∀ w ∈ I4, ¬ G.Adj u w := by simp only [SimpleGraph.fromRel_adj]; decide

lemma one_le {α : Type} {S : Finset α} {a : α} (ha : a ∈ S) : 1 ≤ S.card :=
  Finset.card_pos.mpr ⟨a, ha⟩

lemma two_le {α : Type} [DecidableEq α] {S : Finset α} {a b : α} (ha : a ∈ S) (hb : b ∈ S)
    (h : a ≠ b) : 2 ≤ S.card := by
  rw [← Finset.card_pair h]
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

lemma three_le {α : Type} [DecidableEq α] {S : Finset α} {a b c : α} (ha : a ∈ S) (hb : b ∈ S)
    (hc : c ∈ S) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ S.card := by
  have h3 : ({a, b, c} : Finset α).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← h3]
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

lemma two_le' {α : Type} [DecidableEq α] {S : Finset α} {p q r : α} (hp : p ∈ S) (hq : q ∈ S)
    (hr : r ∈ S) (hne : ¬ (p = q ∧ q = r)) : 2 ≤ S.card := by
  by_cases h : p = q
  · exact two_le hq hr (fun h' => hne ⟨h, h'⟩)
  · exact two_le hp hq h

/-- Triangle vertex `0` met by one rectangle on its three forced cells: the cross cells of that
rectangle keep vertices `1` and `2` apart, and one of them needs three rectangles. -/
lemma V0 {k : ℕ} (R : Sym2 (Fin 6) → Finset (Fin 6) → Fin k)
    (hcross : ∀ e I e' I', Ok e I → Ok e' I' → Ok e I' → R e I = R e' I' → R e I' = R e I)
    (hclash : ∀ e I e' I', Ok e I → Ok e' I' → R e I = R e' I' →
      (∀ y : Fin 6, y ∈ e → y ∉ I → y ∈ e' → y ∉ I' → False) → False)
    (hE : R e03 I4 = R e01 I2 ∧ R e01 I2 = R e02 I3) :
    R e12 I3 ≠ R e01 I1 ∧ R e14 I4 ≠ R e01 I1 ∧ R e02 I1 ≠ R e12 I2 ∧ R e25 I4 ≠ R e02 I1 ∧
      (R e14 I4 ≠ R e12 I3 ∨ R e25 I4 ≠ R e12 I2) := by
  have c1 : R e01 I3 = R e01 I2 :=
    hcross e01 I2 e02 I3 ⟨he01, hI2⟩ ⟨he02, hI3⟩ ⟨he01, hI3⟩ hE.2
  have c2 : R e01 I4 = R e01 I2 :=
    hcross e01 I2 e03 I4 ⟨he01, hI2⟩ ⟨he03, hI4⟩ ⟨he01, hI4⟩ hE.1.symm
  have c3 : R e02 I2 = R e02 I3 :=
    hcross e02 I3 e01 I2 ⟨he02, hI3⟩ ⟨he01, hI2⟩ ⟨he02, hI2⟩ hE.2.symm
  have c4 : R e02 I4 = R e02 I3 :=
    hcross e02 I3 e03 I4 ⟨he02, hI3⟩ ⟨he03, hI4⟩ ⟨he02, hI4⟩ (hE.2.symm.trans hE.1.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have x := hcross e01 I1 e12 I3 ⟨he01, hI1⟩ ⟨he12, hI3⟩ ⟨he01, hI3⟩ h.symm
    exact hclash e01 I2 e12 I3 ⟨he01, hI2⟩ ⟨he12, hI3⟩ (c1.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e01 I1 e14 I4 ⟨he01, hI1⟩ ⟨he14, hI4⟩ ⟨he01, hI4⟩ h.symm
    exact hclash e01 I2 e14 I4 ⟨he01, hI2⟩ ⟨he14, hI4⟩ (c2.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e02 I1 e12 I2 ⟨he02, hI1⟩ ⟨he12, hI2⟩ ⟨he02, hI2⟩ h
    exact hclash e02 I3 e12 I2 ⟨he02, hI3⟩ ⟨he12, hI2⟩ (c3.symm.trans (x.trans h))
      (by decide)
  · intro h
    have x := hcross e02 I1 e25 I4 ⟨he02, hI1⟩ ⟨he25, hI4⟩ ⟨he02, hI4⟩ h.symm
    exact hclash e02 I3 e25 I4 ⟨he02, hI3⟩ ⟨he25, hI4⟩ (c4.symm.trans (x.trans h.symm))
      (by decide)
  · by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    have x := hcross e12 I3 e14 I4 ⟨he12, hI3⟩ ⟨he14, hI4⟩ ⟨he12, hI4⟩ hcon.1.symm
    have y := hcross e12 I2 e25 I4 ⟨he12, hI2⟩ ⟨he25, hI4⟩ ⟨he12, hI4⟩ hcon.2.symm
    exact hclash e12 I3 e12 I2 ⟨he12, hI3⟩ ⟨he12, hI2⟩ (x.symm.trans y) (by decide)

/-- Triangle vertex `1` met by one rectangle on its three forced cells: the cross cells of that
rectangle keep vertices `2` and `0` apart, and one of them needs three rectangles. -/
lemma V1 {k : ℕ} (R : Sym2 (Fin 6) → Finset (Fin 6) → Fin k)
    (hcross : ∀ e I e' I', Ok e I → Ok e' I' → Ok e I' → R e I = R e' I' → R e I' = R e I)
    (hclash : ∀ e I e' I', Ok e I → Ok e' I' → R e I = R e' I' →
      (∀ y : Fin 6, y ∈ e → y ∉ I → y ∈ e' → y ∉ I' → False) → False)
    (hE : R e14 I4 = R e12 I3 ∧ R e12 I3 = R e01 I1) :
    R e02 I1 ≠ R e12 I2 ∧ R e25 I4 ≠ R e12 I2 ∧ R e01 I2 ≠ R e02 I3 ∧ R e03 I4 ≠ R e01 I2 ∧
      (R e25 I4 ≠ R e02 I1 ∨ R e03 I4 ≠ R e02 I3) := by
  have c1 : R e12 I1 = R e12 I3 :=
    hcross e12 I3 e01 I1 ⟨he12, hI3⟩ ⟨he01, hI1⟩ ⟨he12, hI1⟩ hE.2
  have c2 : R e12 I4 = R e12 I3 :=
    hcross e12 I3 e14 I4 ⟨he12, hI3⟩ ⟨he14, hI4⟩ ⟨he12, hI4⟩ hE.1.symm
  have c3 : R e01 I3 = R e01 I1 :=
    hcross e01 I1 e12 I3 ⟨he01, hI1⟩ ⟨he12, hI3⟩ ⟨he01, hI3⟩ hE.2.symm
  have c4 : R e01 I4 = R e01 I1 :=
    hcross e01 I1 e14 I4 ⟨he01, hI1⟩ ⟨he14, hI4⟩ ⟨he01, hI4⟩ (hE.2.symm.trans hE.1.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have x := hcross e12 I2 e02 I1 ⟨he12, hI2⟩ ⟨he02, hI1⟩ ⟨he12, hI1⟩ h.symm
    exact hclash e12 I3 e02 I1 ⟨he12, hI3⟩ ⟨he02, hI1⟩ (c1.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e12 I2 e25 I4 ⟨he12, hI2⟩ ⟨he25, hI4⟩ ⟨he12, hI4⟩ h.symm
    exact hclash e12 I3 e25 I4 ⟨he12, hI3⟩ ⟨he25, hI4⟩ (c2.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e01 I2 e02 I3 ⟨he01, hI2⟩ ⟨he02, hI3⟩ ⟨he01, hI3⟩ h
    exact hclash e01 I1 e02 I3 ⟨he01, hI1⟩ ⟨he02, hI3⟩ (c3.symm.trans (x.trans h))
      (by decide)
  · intro h
    have x := hcross e01 I2 e03 I4 ⟨he01, hI2⟩ ⟨he03, hI4⟩ ⟨he01, hI4⟩ h.symm
    exact hclash e01 I1 e03 I4 ⟨he01, hI1⟩ ⟨he03, hI4⟩ (c4.symm.trans (x.trans h.symm))
      (by decide)
  · by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    have x := hcross e02 I1 e25 I4 ⟨he02, hI1⟩ ⟨he25, hI4⟩ ⟨he02, hI4⟩ hcon.1.symm
    have y := hcross e02 I3 e03 I4 ⟨he02, hI3⟩ ⟨he03, hI4⟩ ⟨he02, hI4⟩ hcon.2.symm
    exact hclash e02 I1 e02 I3 ⟨he02, hI1⟩ ⟨he02, hI3⟩ (x.symm.trans y) (by decide)

/-- Triangle vertex `2` met by one rectangle on its three forced cells: the cross cells of that
rectangle keep vertices `0` and `1` apart, and one of them needs three rectangles. -/
lemma V2 {k : ℕ} (R : Sym2 (Fin 6) → Finset (Fin 6) → Fin k)
    (hcross : ∀ e I e' I', Ok e I → Ok e' I' → Ok e I' → R e I = R e' I' → R e I' = R e I)
    (hclash : ∀ e I e' I', Ok e I → Ok e' I' → R e I = R e' I' →
      (∀ y : Fin 6, y ∈ e → y ∉ I → y ∈ e' → y ∉ I' → False) → False)
    (hE : R e25 I4 = R e02 I1 ∧ R e02 I1 = R e12 I2) :
    R e01 I2 ≠ R e02 I3 ∧ R e03 I4 ≠ R e02 I3 ∧ R e12 I3 ≠ R e01 I1 ∧ R e14 I4 ≠ R e12 I3 ∧
      (R e03 I4 ≠ R e01 I2 ∨ R e14 I4 ≠ R e01 I1) := by
  have c1 : R e02 I2 = R e02 I1 :=
    hcross e02 I1 e12 I2 ⟨he02, hI1⟩ ⟨he12, hI2⟩ ⟨he02, hI2⟩ hE.2
  have c2 : R e02 I4 = R e02 I1 :=
    hcross e02 I1 e25 I4 ⟨he02, hI1⟩ ⟨he25, hI4⟩ ⟨he02, hI4⟩ hE.1.symm
  have c3 : R e12 I1 = R e12 I2 :=
    hcross e12 I2 e02 I1 ⟨he12, hI2⟩ ⟨he02, hI1⟩ ⟨he12, hI1⟩ hE.2.symm
  have c4 : R e12 I4 = R e12 I2 :=
    hcross e12 I2 e25 I4 ⟨he12, hI2⟩ ⟨he25, hI4⟩ ⟨he12, hI4⟩ (hE.2.symm.trans hE.1.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have x := hcross e02 I3 e01 I2 ⟨he02, hI3⟩ ⟨he01, hI2⟩ ⟨he02, hI2⟩ h.symm
    exact hclash e02 I1 e01 I2 ⟨he02, hI1⟩ ⟨he01, hI2⟩ (c1.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e02 I3 e03 I4 ⟨he02, hI3⟩ ⟨he03, hI4⟩ ⟨he02, hI4⟩ h.symm
    exact hclash e02 I1 e03 I4 ⟨he02, hI1⟩ ⟨he03, hI4⟩ (c2.symm.trans (x.trans h.symm))
      (by decide)
  · intro h
    have x := hcross e12 I3 e01 I1 ⟨he12, hI3⟩ ⟨he01, hI1⟩ ⟨he12, hI1⟩ h
    exact hclash e12 I2 e01 I1 ⟨he12, hI2⟩ ⟨he01, hI1⟩ (c3.symm.trans (x.trans h))
      (by decide)
  · intro h
    have x := hcross e12 I3 e14 I4 ⟨he12, hI3⟩ ⟨he14, hI4⟩ ⟨he12, hI4⟩ h.symm
    exact hclash e12 I2 e14 I4 ⟨he12, hI2⟩ ⟨he14, hI4⟩ (c4.symm.trans (x.trans h.symm))
      (by decide)
  · by_contra hcon
    simp only [not_or, ne_eq, not_not] at hcon
    have x := hcross e01 I2 e03 I4 ⟨he01, hI2⟩ ⟨he03, hI4⟩ ⟨he01, hI4⟩ hcon.1.symm
    have y := hcross e01 I1 e14 I4 ⟨he01, hI1⟩ ⟨he14, hI4⟩ ⟨he01, hI4⟩ hcon.2.symm
    exact hclash e01 I2 e01 I1 ⟨he01, hI2⟩ ⟨he01, hI1⟩ (x.symm.trans y) (by decide)

end PEqualNP.Outside.L_meta_462_aux

open PEqualNP.Outside.L_meta_462_aux in
theorem PEqualNP.Outside.L_meta_462 : ∀ (k : ℕ) (A : Fin k → Finset (Sym2 (Fin 6))) (B : Fin k → Finset (Finset (Fin 6)))
    (t : Fin k → Fin 6),
    (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).edgeFinset ∧ t i ∈ e) →
    (∀ i, ∀ I ∈ B i, t i ∉ I) →
    (∀ e ∈ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).edgeFinset,
      ∀ I : Finset (Fin 6), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 6 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 4) ∨ (a = 2 ∧ b = 5))).Adj u w) →
        ∃! i : Fin k, e ∈ A i ∧ I ∈ B i) →
    9 ≤ k := by
  intro k A B t h1 h2 h3
  classical
  have h3' : ∀ e I, Ok e I → ∃! i : Fin k, e ∈ A i ∧ I ∈ B i :=
    fun e I h => h3 e (SimpleGraph.mem_edgeFinset.mpr h.1) I h.2
  obtain ⟨i0, -⟩ := (h3' e01 I1 ⟨he01, hI1⟩).exists
  obtain ⟨R, hmem⟩ : ∃ R : Sym2 (Fin 6) → Finset (Fin 6) → Fin k,
      ∀ e I, Ok e I → e ∈ A (R e I) ∧ I ∈ B (R e I) :=
    ⟨fun e I => if h : Ok e I then (h3' e I h).exists.choose else i0, by
      intro e I h
      simp only [dif_pos h]
      exact (h3' e I h).exists.choose_spec⟩
  have huniq : ∀ e I j, Ok e I → e ∈ A j → I ∈ B j → j = R e I := by
    intro e I j h ha hb
    exact (h3' e I h).unique ⟨ha, hb⟩ (hmem e I h)
  have hcross : ∀ e I e' I', Ok e I → Ok e' I' → Ok e I' → R e I = R e' I' →
      R e I' = R e I := by
    intro e I e' I' h h' h'' heq
    refine (huniq e I' _ h'' (hmem e I h).1 ?_).symm
    rw [heq]; exact (hmem e' I' h').2
  have hclash : ∀ e I e' I', Ok e I → Ok e' I' → R e I = R e' I' →
      (∀ y : Fin 6, y ∈ e → y ∉ I → y ∈ e' → y ∉ I' → False) → False := by
    intro e I e' I' h h' heq hy
    refine hy (t (R e I)) (h1 _ e (hmem e I h).1).2 (h2 _ I (hmem e I h).2) ?_ ?_
    · rw [heq]; exact (h1 _ e' (hmem e' I' h').1).2
    · rw [heq]; exact h2 _ I' (hmem e' I' h').2
  obtain ⟨S, hSd⟩ : ∃ S : Fin 6 → Finset (Fin k), ∀ v i, i ∈ S v ↔ t i = v :=
    ⟨fun v => Finset.univ.filter (fun i => t i = v), by simp⟩
  have hk : k = (S 0).card + (S 1).card + (S 2).card + (S 3).card + (S 4).card + (S 5).card := by
    have hSeq : ∀ v, S v = Finset.univ.filter (fun i => t i = v) := fun v => by
      ext i; simp [hSd]
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin k)))
      (t := (Finset.univ : Finset (Fin 6))) (f := t) (fun _ _ => Finset.mem_univ _)
    rw [Fin.sum_univ_six] at this
    simpa [hSeq] using this
  have hS : ∀ e I (v : Fin 6), Ok e I → (∀ y : Fin 6, y ∈ e → y ∉ I → y = v) → R e I ∈ S v :=
    fun e I v h hy => (hSd v _).mpr (hy _ (h1 _ e (hmem e I h).1).2 (h2 _ I (hmem e I h).2))
  have m3 : R e03 I1 ∈ S 3 := hS _ _ _ ⟨he03, hI1⟩ (by decide)
  have m4 : R e14 I2 ∈ S 4 := hS _ _ _ ⟨he14, hI2⟩ (by decide)
  have m5 : R e25 I3 ∈ S 5 := hS _ _ _ ⟨he25, hI3⟩ (by decide)
  have mp0 : R e03 I4 ∈ S 0 := hS _ _ _ ⟨he03, hI4⟩ (by decide)
  have mq0 : R e01 I2 ∈ S 0 := hS _ _ _ ⟨he01, hI2⟩ (by decide)
  have mr0 : R e02 I3 ∈ S 0 := hS _ _ _ ⟨he02, hI3⟩ (by decide)
  have mp1 : R e14 I4 ∈ S 1 := hS _ _ _ ⟨he14, hI4⟩ (by decide)
  have mq1 : R e12 I3 ∈ S 1 := hS _ _ _ ⟨he12, hI3⟩ (by decide)
  have mr1 : R e01 I1 ∈ S 1 := hS _ _ _ ⟨he01, hI1⟩ (by decide)
  have mp2 : R e25 I4 ∈ S 2 := hS _ _ _ ⟨he25, hI4⟩ (by decide)
  have mq2 : R e02 I1 ∈ S 2 := hS _ _ _ ⟨he02, hI1⟩ (by decide)
  have mr2 : R e12 I2 ∈ S 2 := hS _ _ _ ⟨he12, hI2⟩ (by decide)
  have c3 := one_le m3
  have c4 := one_le m4
  have c5 := one_le m5
  by_cases h0 : R e03 I4 = R e01 I2 ∧ R e01 I2 = R e02 I3
  · obtain ⟨a, b, c, d, e⟩ := V0 R hcross hclash h0
    have x0 := one_le mp0
    have x1 := two_le mq1 mr1 a
    have x2 := two_le mq2 mr2 c
    rcases e with e | e
    · have := three_le mp1 mq1 mr1 e b a; omega
    · have := three_le mp2 mq2 mr2 d e c; omega
  by_cases h1' : R e14 I4 = R e12 I3 ∧ R e12 I3 = R e01 I1
  · obtain ⟨a, b, c, d, e⟩ := V1 R hcross hclash h1'
    have x0 := one_le mp1
    have x1 := two_le mq2 mr2 a
    have x2 := two_le mq0 mr0 c
    rcases e with e | e
    · have := three_le mp2 mq2 mr2 e b a; omega
    · have := three_le mp0 mq0 mr0 d e c; omega
  by_cases h2' : R e25 I4 = R e02 I1 ∧ R e02 I1 = R e12 I2
  · obtain ⟨a, b, c, d, e⟩ := V2 R hcross hclash h2'
    have x0 := one_le mp2
    have x1 := two_le mq0 mr0 a
    have x2 := two_le mq1 mr1 c
    rcases e with e | e
    · have := three_le mp0 mq0 mr0 e b a; omega
    · have := three_le mp1 mq1 mr1 d e c; omega
  have y0 := two_le' mp0 mq0 mr0 h0
  have y1 := two_le' mp1 mq1 mr1 h1'
  have y2 := two_le' mp2 mq2 mr2 h2'
  omega
