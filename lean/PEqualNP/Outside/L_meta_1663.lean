import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1663

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) := by
  intro q N L v s p Mv Ms Mp _ _ _ hint hnc hsMv hpMv hpMs hvMs hvMp hsMp S hvS hsS hpS
  have key : ∀ a b : Fin N, a ≠ b → ∀ x y : Fin N, x ∈ L a → x ∈ L b → y ∈ L a → y ∈ L b →
      x = y := by
    intro a b hab x y hxa hxb hya hyb
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hint a b hab)
    have hx : x ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hxa, hxb⟩
    have hy : y ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hya, hyb⟩
    rw [hc] at hx hy
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hsp : s ≠ p := by
    intro h
    have h2 : p ∈ L Mp := by
      rw [← h]
      exact hsMp
    exact hnc Mp ⟨hvMp, hsMp, h2⟩
  refine ⟨?_, ?_⟩
  · intro w W hwW P hP hh
    obtain ⟨h1, h2⟩ := hh
    have hwS : w ∉ L S := by
      rcases hwW with hw | hw
      · rw [hw.1]
        exact hsS
      · rw [hw.1]
        exact hpS
    have hPS : P ∈ L S := by
      rcases h1 with h | h
      · exact h
      · exact absurd h.2.2.2 hwS
    have hSW : S ≠ W := by
      intro h
      rcases hwW with hw | hw
      · rw [h, hw.2] at hpS
        exact hpS hpMs
      · rw [h, hw.2] at hsS
        exact hsS hsMp
    have hvW : v ∈ L W := by
      rcases hwW with hw | hw
      · rw [hw.2]
        exact hvMs
      · rw [hw.2]
        exact hvMp
    have hPv : P = v := key S W hSW P v hPS hP hvS hvW
    rcases h2 with h | h
    · rw [hPv] at h
      exact hvMv h
    · exact h.1 hPv
  · intro w S1 hw hwS1 hS1 P hP hh
    obtain ⟨h1, h2⟩ := hh
    have hwS : w ∉ L S := by
      rcases hw with hw | hw
      · rw [hw]
        exact hsS
      · rw [hw]
        exact hpS
    have hvS1 : v ∉ L S1 := by
      intro h
      have hvw : v = w := hS1 v (Or.inl rfl) h
      rw [← hvw] at hwS
      exact hwS hvS
    have hPS1 : P ∈ L S1 := by
      rcases h2 with h | h
      · exact h
      · exact absurd h.2.2.2 hvS1
    have hMS1 : Mv ≠ S1 := by
      intro h
      rw [← h] at hS1
      have e1 : s = w := hS1 s (Or.inr (Or.inl rfl)) hsMv
      have e2 : p = w := hS1 p (Or.inr (Or.inr rfl)) hpMv
      exact hsp (e1.trans e2.symm)
    have hwMv : w ∈ L Mv := by
      rcases hw with hw | hw
      · rw [hw]
        exact hsMv
      · rw [hw]
        exact hpMv
    have hPw : P = w := key Mv S1 hMS1 P w hP hPS1 hwMv hwS1
    rcases h1 with h | h
    · rw [hPw] at h
      exact hwS h
    · rcases hw with hw | hw
      · exact h.2.1 (hPw.trans hw)
      · exact h.2.2.1 (hPw.trans hw)

end PEqualNP.Outside.L_meta_1663

theorem PEqualNP.Outside.L_meta_1663 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ w W : Fin N, (w = s ∧ W = Ms ∨ w = p ∧ W = Mp) → ∀ P ∈ L W,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ w ∈ L Mv)))) ∧
    (∀ w S1 : Fin N, (w = s ∨ w = p) → w ∈ L S1 → (∀ u : Fin N, (u = v ∨ u = s ∨ u = p) → u ∈ L S1 → u = w) → ∀ P ∈ L Mv,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S)) ∧ (P ∈ L S1 ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ v ∈ L S1)))) :=
  PEqualNP.Outside.L_meta_1663.main_aux
