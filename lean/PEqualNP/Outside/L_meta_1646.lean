import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1646

theorem key {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : PEqualNP.TopForm.NoFourCycle G) {a b x c : Fin n} (hab : a ≠ b)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hca : G.Adj c a) (hcb : G.Adj c b) : x = c := by
  have h1 := h a b hab
  rw [Finset.card_le_one] at h1
  exact h1 x (by simp [hxa.symm, hxb.symm]) c (by simp [hca.symm, hcb.symm])

theorem blk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (Y : Finset (Fin n)) (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (B : Finset (Fin n))
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U)) :
    (B ∩ Y).card ≤ 1 := by
  rcases hB with h1 | ⟨_, c, hc, hcU⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans (le_of_eq h1)
  · have hadj : ∀ y ∈ Y, G.Adj x y := fun y hy => by
      have h2 := hU _ (hY y hy)
      rwa [SimpleGraph.mem_edgeSet] at h2
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha2 := Finset.mem_inter.mp ha
    have hb2 := Finset.mem_inter.mp hb
    have hxc := key G hG hab (hadj a ha2.2) (hadj b hb2.2) (hc a ha2.1) (hc b hb2.1)
    subst hxc
    exact hcU a ha2.1 (hY a ha2.2)

theorem blk0 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : PEqualNP.TopForm.NoFourCycle G) (U : Finset (Sym2 (Fin n)))
    (hU : ∀ e ∈ U, e ∈ G.edgeSet) (x : Fin n) (Y : Finset (Fin n)) (hY : ∀ y ∈ Y, s(x, y) ∈ U)
    (B : Finset (Fin n))
    (hB : B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))
    (hx : ∀ b ∈ B, G.Adj x b) (r : Fin n) (hr : r ∈ B) (hrY : r ∉ Y) :
    (B ∩ Y).card = 0 := by
  rw [Finset.card_eq_zero]
  by_contra hne
  obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hy2 := Finset.mem_inter.mp hy
  have hyr : y ≠ r := fun h => hrY (h ▸ hy2.2)
  rcases hB with h1 | ⟨_, c, hc, hcU⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha, Finset.mem_singleton] at hr
    have hya := hy2.1
    rw [ha, Finset.mem_singleton] at hya
    exact hyr (hya.trans hr.symm)
  · have hadj : G.Adj x y := by
      have h2 := hU _ (hY y hy2.2)
      rwa [SimpleGraph.mem_edgeSet] at h2
    have hxc := key G hG hyr hadj (hx r hr) (hc y hy2.1) (hc r hr)
    subst hxc
    exact hcU y hy2.1 (hY y hy2.2)

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G inst hG U hU x Y hY R π hπ hcover
  have hcov : R ∩ Y ⊆ π.biUnion (fun B => B ∩ Y) := by
    intro y hy
    have hy2 := Finset.mem_inter.mp hy
    obtain ⟨B, hB, hyB⟩ := hcover y hy2.1
    exact Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_inter.mpr ⟨hyB, hy2.2⟩⟩
  have h1 : (R ∩ Y).card ≤ ∑ B ∈ π, (B ∩ Y).card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have hb : ∀ B ∈ π, (B ∩ Y).card ≤ 1 := fun B hB => blk G hG U hU x Y hY B (hπ B hB).2
  constructor
  · have h2 := Finset.sum_le_card_nsmul π (fun B => (B ∩ Y).card) 1 hb
    simp only [smul_eq_mul, mul_one] at h2
    exact h1.trans h2
  · intro hx hnot
    obtain ⟨r, hrR, hrY⟩ := Finset.not_subset.mp hnot
    obtain ⟨B0, hB0, hrB0⟩ := hcover r hrR
    have h0 : (B0 ∩ Y).card = 0 :=
      blk0 G hG U hU x Y hY B0 (hπ B0 hB0).2 (fun b hb0 => hx b ((hπ B0 hB0).1 hb0)) r hrB0 hrY
    have h3 := Finset.sum_erase_add π (fun B => (B ∩ Y).card) hB0
    have h4 := Finset.sum_le_card_nsmul (π.erase B0) (fun B => (B ∩ Y).card) 1
      (fun B hB => hb B (Finset.mem_of_mem_erase hB))
    simp only [smul_eq_mul, mul_one] at h4
    rw [Finset.card_erase_of_mem hB0] at h4
    have h5 : 0 < π.card := Finset.card_pos.mpr ⟨B0, hB0⟩
    omega

end PEqualNP.Outside.L_meta_1646

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) :=
  PEqualNP.Outside.L_meta_1646.main_aux
