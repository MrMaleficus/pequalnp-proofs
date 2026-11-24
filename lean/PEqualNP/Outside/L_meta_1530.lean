import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1530

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ hG P Q W hW
  have hG2 : ∀ a b : Fin n, a ≠ b →
      (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hG
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hQ
    by_contra hcon
    have hcon2 : 1 < (W ∩ P).card := by omega
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hcon2
    rw [Finset.mem_inter] at hw1 hw2
    have hsub : Q ⊆ Finset.univ.filter fun w => G.Adj w1 w ∧ G.Adj w2 w := by
      intro q hq
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases (hW w1).mp hw1.1 w1 hw1.2 q hq with h | h | h
        · exact h
        · exact absurd rfl (G.ne_of_adj h)
        · exact h.symm
      · rcases (hW w2).mp hw2.1 w2 hw2.2 q hq with h | h | h
        · exact h
        · exact absurd rfl (G.ne_of_adj h)
        · exact h.symm
    have h1 := Finset.card_le_card hsub
    have h2 := hG2 w1 w2 hne
    omega
  · intro hP
    by_contra hcon
    have hcon2 : 1 < (W ∩ Q).card := by omega
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hcon2
    rw [Finset.mem_inter] at hw1 hw2
    have hsub : P ⊆ Finset.univ.filter fun w => G.Adj w1 w ∧ G.Adj w2 w := by
      intro p hp
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases (hW w1).mp hw1.1 p hp w1 hw1.2 with h | h | h
        · exact h.symm
        · exact h.symm
        · exact absurd rfl (G.ne_of_adj h)
      · rcases (hW w2).mp hw2.1 p hp w2 hw2.2 with h | h | h
        · exact h.symm
        · exact h.symm
        · exact absurd rfl (G.ne_of_adj h)
    have h1 := Finset.card_le_card hsub
    have h2 := hG2 w1 w2 hne
    omega
  · intro a b _ hP hQ ha
    have hnot : ¬ (a ∈ P ∧ a ∈ Q) := by
      rintro ⟨h1, h2⟩
      rcases (hW a).mp ha a h1 a h2 with h | h | h
      · exact G.ne_of_adj h rfl
      · exact G.ne_of_adj h rfl
      · exact G.ne_of_adj h rfl
    refine ⟨?_, ?_, ?_⟩
    · intro h1
      rcases hQ with h | h
      · exact absurd ⟨h1, h⟩ hnot
      · exact h
    · intro h2
      rcases hP with h | h
      · exact absurd ⟨h, h2⟩ hnot
      · exact h
    · intro h1 h2
      rw [Finset.mem_inter]
      exact ⟨hP.resolve_left h1, hQ.resolve_left h2⟩
  · intro s hs u hus
    have hsP : s ∈ P ∩ Q := by rw [hs]; exact Finset.mem_singleton_self s
    rw [Finset.mem_inter] at hsP
    have hsub : (Finset.univ.filter fun w => G.Adj u w) ∩ W ⊆
        Finset.univ.filter fun w => G.Adj u w ∧ G.Adj s w := by
      intro w hw
      rw [Finset.mem_inter, Finset.mem_filter] at hw
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hw.1.2, ?_⟩
      rcases (hW w).mp hw.2 s hsP.1 s hsP.2 with h | h | h
      · exact absurd rfl (G.ne_of_adj h)
      · exact h
      · exact h
    exact le_trans (Finset.card_le_card hsub) (hG2 u s hus)

end PEqualNP.Outside.L_meta_1530

theorem PEqualNP.Outside.L_meta_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) :=
  PEqualNP.Outside.L_meta_1530.main_aux
