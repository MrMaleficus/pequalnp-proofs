import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1662

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ Q ∈ L S, Q ≠ v → Q ∉ L Mp ∧ p ∉ L Mp ∧
      ∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → Q ∉ L S2 ∧ p ∉ L S2) ∧
    (∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → ∀ B : Fin N, (B = s ∨ B = p) → ∀ P ∈ L S2,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L Mv)))) ∧
    (∀ K : Fin N, v ∉ L K → s ∉ L K → p ∉ L K → ∀ B : Fin N, (B = v ∨ B = s ∨ B = p) →
      ∀ P1 ∈ L K, ∀ P2 ∈ L K, (P1 ∈ L S ∨ B ∈ L S) → (P1 ∈ L Mv ∨ B ∈ L Mv) →
        (P2 ∈ L S ∨ B ∈ L S) → (P2 ∈ L Mv ∨ B ∈ L Mv) → P1 = P2) ∧
    v ∉ L Mv := by
  intro q N L v s p Mv Ms Mp _ _ _ hint hnc hsMv hpMv _ _ hvMp hsMp S hvS hsS hpS
  have key : ∀ a b : Fin N, a ≠ b → ∀ x y : Fin N, x ∈ L a → x ∈ L b → y ∈ L a → y ∈ L b →
      x = y := by
    intro a b hab x y hxa hxb hya hyb
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hint a b hab)
    have hx : x ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hxa, hxb⟩
    have hy : y ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨hya, hyb⟩
    rw [hc] at hx hy
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
  have hpMp : p ∉ L Mp := fun h => hnc Mp ⟨hvMp, hsMp, h⟩
  have hvMv : v ∉ L Mv := fun h => hnc Mv ⟨h, hsMv, hpMv⟩
  have hSMp : S ≠ Mp := by
    intro h
    rw [h] at hsS
    exact hsS hsMp
  refine ⟨?_, ?_, ?_, hvMv⟩
  · intro Q hQ hQv
    refine ⟨fun h => hQv (key S Mp hSMp Q v hQ h hvS hvMp), hpMp, ?_⟩
    intro S2 hne hvS2 _ hpS2
    exact ⟨fun h => hQv (key S S2 (Ne.symm hne) Q v hQ h hvS hvS2), hpS2⟩
  · intro S2 hne hvS2 _ _ B hB P hP hh
    obtain ⟨h1, h2⟩ := hh
    have hBS : B ∉ L S := by
      rcases hB with hB | hB
      · rw [hB]
        exact hsS
      · rw [hB]
        exact hpS
    have hPS : P ∈ L S := by
      rcases h1 with h | h
      · exact h
      · exact absurd h.2.2.2 hBS
    have hPv : P = v := key S S2 (Ne.symm hne) P v hPS hP hvS hvS2
    rcases h2 with h | h
    · rw [hPv] at h
      exact hvMv h
    · exact h.1 hPv
  · intro K hvK hsK _ B hB P1 hP1 P2 hP2 h1 h2 h3 h4
    have hKS : K ≠ S := by
      intro h
      rw [h] at hvK
      exact hvK hvS
    have hKMv : K ≠ Mv := by
      intro h
      rw [h] at hsK
      exact hsK hsMv
    rcases hB with hB | hB | hB
    · rw [hB] at h2 h4
      exact key K Mv hKMv P1 P2 hP1 (h2.resolve_right hvMv) hP2 (h4.resolve_right hvMv)
    · rw [hB] at h1 h3
      exact key K S hKS P1 P2 hP1 (h1.resolve_right hsS) hP2 (h3.resolve_right hsS)
    · rw [hB] at h1 h3
      exact key K S hKS P1 P2 hP1 (h1.resolve_right hpS) hP2 (h3.resolve_right hpS)

end PEqualNP.Outside.L_meta_1662

theorem PEqualNP.Outside.L_meta_1662 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (v s p Mv Ms Mp : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ i : Fin N, ¬ (v ∈ L i ∧ s ∈ L i ∧ p ∈ L i)) →
    s ∈ L Mv → p ∈ L Mv → p ∈ L Ms → v ∈ L Ms → v ∈ L Mp → s ∈ L Mp →
    ∀ S : Fin N, v ∈ L S → s ∉ L S → p ∉ L S →
    (∀ Q ∈ L S, Q ≠ v → Q ∉ L Mp ∧ p ∉ L Mp ∧
      ∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → Q ∉ L S2 ∧ p ∉ L S2) ∧
    (∀ S2 : Fin N, S2 ≠ S → v ∈ L S2 → s ∉ L S2 → p ∉ L S2 → ∀ B : Fin N, (B = s ∨ B = p) → ∀ P ∈ L S2,
      ¬ ((P ∈ L S ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L S)) ∧ (P ∈ L Mv ∨ (P ≠ v ∧ P ≠ s ∧ P ≠ p ∧ B ∈ L Mv)))) ∧
    (∀ K : Fin N, v ∉ L K → s ∉ L K → p ∉ L K → ∀ B : Fin N, (B = v ∨ B = s ∨ B = p) →
      ∀ P1 ∈ L K, ∀ P2 ∈ L K, (P1 ∈ L S ∨ B ∈ L S) → (P1 ∈ L Mv ∨ B ∈ L Mv) →
        (P2 ∈ L S ∨ B ∈ L S) → (P2 ∈ L Mv ∨ B ∈ L Mv) → P1 = P2) ∧
    v ∉ L Mv :=
  PEqualNP.Outside.L_meta_1662.main_aux
