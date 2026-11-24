import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1533

theorem key {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) {a b x c : Fin n} (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hca : G.Adj c a) (hcb : G.Adj c b) : x = c := by
  have h1 := h a b hab
  rw [Finset.card_le_one] at h1
  exact h1 x (by simp [hxa.symm, hxb.symm]) c (by simp [hca.symm, hcb.symm])

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G →
    ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) →
    ∀ (B : Finset (Fin n)), (2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) →
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) := by
  rintro n G inst hG U hU x Y hY B ⟨hB, c, hc, hcU⟩
  have hxc : ∀ y ∈ B ∩ Y, x ≠ c := by
    intro y hy hxc
    rw [Finset.mem_inter] at hy
    subst hxc
    exact hcU y hy.1 (hY y hy.2)
  have hadj : ∀ y ∈ Y, G.Adj x y := fun y hy => by
    have h2 := hU _ (hY y hy)
    rwa [SimpleGraph.mem_edgeSet] at h2
  constructor
  · rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha2 := Finset.mem_inter.mp ha
    have hb2 := Finset.mem_inter.mp hb
    exact hxc a ha (key G hG hab (hadj a ha2.2) (hadj b hb2.2) (hc a ha2.1) (hc b hb2.1))
  · intro hx
    by_contra hne
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hy2 := Finset.mem_inter.mp hy
    obtain ⟨b, hb, hby⟩ : ∃ b ∈ B, b ≠ y := Finset.exists_mem_ne (by omega) y
    exact hxc y hy (key G hG (Ne.symm hby) (hadj y hy2.2) (hx b hb) (hc y hy2.1) (hc b hb))

end PEqualNP.Outside.L_meta_1533

theorem PEqualNP.Outside.L_meta_1533 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G →
    ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) →
    ∀ (B : Finset (Fin n)), (2 ≤ B.card ∧ ∃ c : Fin n, (∀ y ∈ B, G.Adj c y) ∧ ∀ y ∈ B, s(c, y) ∉ U) →
    (B ∩ Y).card ≤ 1 ∧ ((∀ b ∈ B, G.Adj x b) → B ∩ Y = ∅) :=
  PEqualNP.Outside.L_meta_1533.main_aux
