import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2408

theorem three_cover {α : Type} [DecidableEq α] (L A B C : Finset α) (h : L ⊆ A ∪ (B ∪ C)) (hA : A.card ≤ 1) (hB : B.card ≤ 1) (hC : C.card ≤ 1) : L.card ≤ 3 := by
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_union_le A (B ∪ C)
  have h3 := Finset.card_union_le B C
  omega

theorem main_aux : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M)) (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a) → (∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w') → Wl.card ≤ 4 := by
  classical
  intro N M I Wl mk z hax hmk hcov
  rcases Wl.eq_empty_or_nonempty with he | ⟨w, hw⟩
  · rw [he]; simp
  have hL : (Wl.erase w).card ≤ 3 := by
    obtain ⟨h3, hw3⟩ := hmk w hw
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < (mk w).card)
    have hone : ∀ x ∈ Wl.erase w, ∀ p q : Fin N, p ∈ mk w → q ∈ mk w → p ≠ q → ¬ (I p x ∧ I q x) := by
      intro x hx p q hp hq hpq hh
      exact hax p q x w hpq (Finset.ne_of_mem_erase hx) ⟨hh.1, hh.2, (hw3 p hp).1, (hw3 q hq).1⟩
    have hcv : ∀ x ∈ Wl.erase w, ∀ p ∈ mk w, I p x ∨ I (z p) x := by
      intro x hx p hp
      exact hcov w hw p hp x (Finset.mem_of_mem_erase hx)
    have hpair : ∀ (s : Finset (Fin M)) (p q : Fin N), p ≠ q → (∀ x ∈ s, I p x ∧ I q x) → s.card ≤ 1 := by
      intro s p q hpq hs
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hxy
      exact hax p q x y hpq hxy ⟨(hs x hx).1, (hs x hx).2, (hs y hy).1, (hs y hy).2⟩
    by_cases hinj : z a ≠ z b ∧ z a ≠ z c ∧ z b ≠ z c
    · obtain ⟨h1, h2, h3'⟩ := hinj
      have hsub : Wl.erase w ⊆ ((Wl.erase w).filter (fun x => I (z a) x ∧ I (z b) x)) ∪ (((Wl.erase w).filter (fun x => I (z a) x ∧ I (z c) x)) ∪ ((Wl.erase w).filter (fun x => I (z b) x ∧ I (z c) x))) := by
        intro x hx
        have e1 := hone x hx a b ha hb hab
        have e2 := hone x hx a c ha hc hac
        have e3 := hone x hx b c hb hc hbc
        have c1 := hcv x hx a ha
        have c2 := hcv x hx b hb
        have c3 := hcv x hx c hc
        simp only [Finset.mem_union, Finset.mem_filter]
        tauto
      have k1 : ((Wl.erase w).filter (fun x => I (z a) x ∧ I (z b) x)).card ≤ 1 :=
        hpair _ (z a) (z b) h1 (fun x hx => (Finset.mem_filter.mp hx).2)
      have k2 : ((Wl.erase w).filter (fun x => I (z a) x ∧ I (z c) x)).card ≤ 1 :=
        hpair _ (z a) (z c) h2 (fun x hx => (Finset.mem_filter.mp hx).2)
      have k3 : ((Wl.erase w).filter (fun x => I (z b) x ∧ I (z c) x)).card ≤ 1 :=
        hpair _ (z b) (z c) h3' (fun x hx => (Finset.mem_filter.mp hx).2)
      exact three_cover _ _ _ _ hsub k1 k2 k3
    · have hex : ∃ p q, p ∈ mk w ∧ q ∈ mk w ∧ p ≠ q ∧ z p = z q := by
        by_contra hno
        apply hinj
        refine ⟨?_, ?_, ?_⟩
        · intro h; exact hno ⟨a, b, ha, hb, hab, h⟩
        · intro h; exact hno ⟨a, c, ha, hc, hac, h⟩
        · intro h; exact hno ⟨b, c, hb, hc, hbc, h⟩
      obtain ⟨p, q, hp, hq, hpq, hz⟩ := hex
      have hthru : ∀ x ∈ Wl.erase w, I (z p) x := by
        intro x hx
        have e := hone x hx p q hp hq hpq
        have c1 := hcv x hx p hp
        have c2 := hcv x hx q hq
        rw [← hz] at c2
        tauto
      rcases (Wl.erase w).eq_empty_or_nonempty with he | ⟨w', hw'⟩
      · rw [he]; simp
      have hw'W : w' ∈ Wl := Finset.mem_of_mem_erase hw'
      obtain ⟨h3', hw3'⟩ := hmk w' hw'W
      have hne : ((mk w').erase (z p)).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.pred_card_le_card_erase (s := mk w') (a := z p)
        omega
      obtain ⟨a', ha'⟩ := hne
      have ha'm : a' ∈ mk w' := Finset.mem_of_mem_erase ha'
      have ha'ne : a' ≠ z p := Finset.ne_of_mem_erase ha'
      obtain ⟨hi1, hi2, hi3⟩ := hw3' a' ha'm
      have hk : ((Wl.erase w).erase w').card ≤ 1 := by
        apply hpair _ (z p) (z a')
        · intro h
          apply hi2
          rw [← h]
          exact hthru w' hw'
        · intro x hx
          have hxL : x ∈ Wl.erase w := Finset.mem_of_mem_erase hx
          have hxw' : x ≠ w' := Finset.ne_of_mem_erase hx
          refine ⟨hthru x hxL, ?_⟩
          rcases hcov w' hw'W a' ha'm x (Finset.mem_of_mem_erase hxL) with h | h
          · exfalso
            exact hax a' (z p) x w' ha'ne hxw' ⟨h, hthru x hxL, hi1, hthru w' hw'⟩
          · exact h
      have := Finset.card_erase_of_mem hw'
      omega
  have := Finset.card_erase_of_mem hw
  omega

end PEqualNP.Outside.L_meta_2408

theorem PEqualNP.Outside.L_meta_2408 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (Wl : Finset (Fin M)) (mk : Fin M → Finset (Fin N)) (z : Fin N → Fin N), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ w ∈ Wl, 3 ≤ (mk w).card ∧ ∀ a ∈ mk w, I a w ∧ ¬ I (z a) w ∧ z a ≠ a) → (∀ w ∈ Wl, ∀ a ∈ mk w, ∀ w' ∈ Wl, I a w' ∨ I (z a) w') → Wl.card ≤ 4 :=
  PEqualNP.Outside.L_meta_2408.main_aux
