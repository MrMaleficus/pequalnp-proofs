import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2577

theorem main_aux : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Sym2 (Fin x1))), PEqualNP.TopForm.NoFourCycle x2 → {x7 ∈ x5 | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 < x4.gates.length, ∃ (x11 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x4 (x1 + x10)).card ∧ (∀ x12 ∈ PEqualNP.TopForm.orIn x1 x4 (x1 + x10), x2.Adj x8 x12) ∧ PEqualNP.TopForm.orIn x1 x4 (PEqualNP.TopForm.opnd x4 x10 x11) = {x9}}.card ≤ (2 : ℕ) * x4.size := by
  classical
  intro n G _ C E hG
  have key : ∀ e : Sym2 (Fin n), (∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
      ∃ j < C.gates.length, ∃ (b : Fin 2),
        2 ≤ (PEqualNP.TopForm.orIn n C (n + j)).card ∧
        (∀ x ∈ PEqualNP.TopForm.orIn n C (n + j), G.Adj u x) ∧
        PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C j b) = {v}) →
      ∃ p : ℕ × Fin 2, p.1 < C.gates.length ∧ ∃ (u : Fin n) (v : Fin n), e = s(u, v) ∧
        2 ≤ (PEqualNP.TopForm.orIn n C (n + p.1)).card ∧
        (∀ x ∈ PEqualNP.TopForm.orIn n C (n + p.1), G.Adj u x) ∧
        PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C p.1 p.2) = {v} := by
    rintro e ⟨u, v, he, j, hj, b, h1, h2, h3⟩
    exact ⟨(j, b), hj, u, v, he, h1, h2, h3⟩
  choose! g hg using key
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  refine le_trans (Finset.card_le_card_of_injOn
    (t := (Finset.range C.gates.length) ×ˢ (Finset.univ : Finset (Fin 2))) g ?_ ?_) ?_
  · intro e he
    have hp := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hg e hp).1, Finset.mem_univ _⟩)
  · intro e he e2 he2 hee
    have hp := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
    have hp2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he2)).2
    obtain ⟨_, u, v, hev, h1, h2, h3⟩ := hg e hp
    obtain ⟨_, u2, v2, hev2, _, k2, k3⟩ := hg e2 hp2
    rw [← hee] at k2 k3
    have hv : v = v2 := Finset.singleton_injective (h3.symm.trans k3)
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_succ_le h1)
    have hc := hG a b hab
    have hu : u = u2 := by
      refine Finset.card_le_one.mp hc u ?_ u2 ?_
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h2 a ha).symm, (h2 b hb).symm⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (k2 a ha).symm, (k2 b hb).symm⟩
    rw [hev, hev2, hu, hv]
  · rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    omega

end PEqualNP.Outside.L_meta_2577

theorem PEqualNP.Outside.L_meta_2577 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Sym2 (Fin x1))), PEqualNP.TopForm.NoFourCycle x2 → {x7 ∈ x5 | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 < x4.gates.length, ∃ (x11 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x4 (x1 + x10)).card ∧ (∀ x12 ∈ PEqualNP.TopForm.orIn x1 x4 (x1 + x10), x2.Adj x8 x12) ∧ PEqualNP.TopForm.orIn x1 x4 (PEqualNP.TopForm.opnd x4 x10 x11) = {x9}}.card ≤ (2 : ℕ) * x4.size :=
  PEqualNP.Outside.L_meta_2577.main_aux
