import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2407

theorem key (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M))
    (H : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 →
      ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (p q z : Fin N) (hpq : p ≠ q)
    (h3 : 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard)
    (hsub : L ⊆ {l2 : Fin M | I q l2 ∨ I z l2}) : p = z := by
  by_contra hpz
  have h3' : 2 < {l : Fin M | l ∈ L ∧ I p l}.ncard := h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp h3'
  obtain ⟨haL, hpa⟩ := ha
  obtain ⟨hbL, hpb⟩ := hb
  obtain ⟨hcL, hpc⟩ := hc
  rcases hsub haL with qa | za <;> rcases hsub hbL with qb | zb <;>
    rcases hsub hcL with qc | zc
  all_goals first
    | exact H p q a b hpq hab ⟨hpa, qa, hpb, qb⟩
    | exact H p q a c hpq hac ⟨hpa, qa, hpc, qc⟩
    | exact H p q b c hpq hbc ⟨hpb, qb, hpc, qc⟩
    | exact H p z a b hpz hab ⟨hpa, za, hpb, zb⟩
    | exact H p z a c hpz hac ⟨hpa, za, hpc, zc⟩
    | exact H p z b c hpz hbc ⟨hpb, zb, hpc, zc⟩

theorem card_aux {α : Type} [Finite α] (S : Set α)
    (h : ∀ q ∈ S, ∃ z, ∀ p ∈ S, p ≠ q → p = z) : S.ncard ≤ 2 := by
  rcases Set.eq_empty_or_nonempty S with hE | ⟨q, hq⟩
  · rw [hE, Set.ncard_empty]
    exact Nat.zero_le 2
  · obtain ⟨z, hz⟩ := h q hq
    have hS : S ⊆ ({q, z} : Set α) := by
      intro p hp
      by_cases hpq : p = q
      · exact Or.inl hpq
      · exact Or.inr (hz p hp hpq)
    have h2 : ({q, z} : Set α).ncard ≤ 2 := by
      have h1 := Set.ncard_insert_le q ({z} : Set α)
      rw [Set.ncard_singleton] at h1
      exact h1
    exact le_trans (Set.ncard_le_ncard hS (Set.toFinite _)) h2

theorem main_aux : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L H
  apply card_aux
  intro q hq
  obtain ⟨-, z, hz⟩ := hq
  refine ⟨z, ?_⟩
  intro p hp hpq
  obtain ⟨hp3, -⟩ := hp
  exact key N M I L H p q z hpq hp3 hz

end PEqualNP.Outside.L_meta_2407

theorem PEqualNP.Outside.L_meta_2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 :=
  PEqualNP.Outside.L_meta_2407.main_aux
