import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1566

def Rb (t u : Fin 13) : Bool :=
  decide ((t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))

def RHS (K : Finset (Fin 13)) : ℕ :=
  (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)

set_option maxRecDepth 100000 in
theorem tri : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    Rb a b = true → Rb a c = true → Rb b c = true →
    ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)),
      ({a, b, c} : Finset (Fin 13)) = {0, l, m} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem quad : ∀ a b c d : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    Rb a b = true → Rb a c = true → Rb b c = true →
    d ≠ a → d ≠ b → d ≠ c →
    Rb d a = true → Rb d b = true → Rb d c = true → False := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem back : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    ∀ t ∈ ({0, l, m} : Finset (Fin 13)), ∀ u ∈ ({0, l, m} : Finset (Fin 13)),
      t ≠ u → Rb t u = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem one : ∀ a : Fin 13, ({a} : Finset (Fin 13)).card - 1 = RHS {a} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem two : ∀ a b : Fin 13, a ≠ b → Rb a b = true →
    ({a, b} : Finset (Fin 13)).card - 1 = RHS {a, b} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem three : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    ({0, l, m} : Finset (Fin 13)).card - 1 = RHS {0, l, m} := by
  decide +kernel

theorem core (Mut : Fin 13 → Fin 13 → Prop)
    (h1 : ∀ t u : Fin 13, Mut t u ↔ ((t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13))))) :
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → Mut t u) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → Mut t u) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  have hb : ∀ t u : Fin 13, Mut t u ↔ Rb t u = true := by
    intro t u
    unfold Rb
    rw [decide_eq_true_iff]
    exact h1 t u
  have p2 : ∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → Mut t u) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m}) := by
    intro K hK
    constructor
    · intro h0
      have h : ∀ t ∈ K, ∀ u ∈ K, t ≠ u → Rb t u = true :=
        fun t ht u hu htu => (hb t u).1 (h0 t ht u hu htu)
      obtain ⟨a, b, c, ha, hbK, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 hK
      have hKeq : K = {a, b, c} := by
        apply Finset.Subset.antisymm
        · intro d hd
          by_contra hd'
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
          exact quad a b c d hab hac hbc (h a ha b hbK hab) (h a ha c hc hac)
            (h b hbK c hc hbc) hd'.1 hd'.2.1 hd'.2.2 (h d hd a ha hd'.1)
            (h d hd b hbK hd'.2.1) (h d hd c hc hd'.2.2)
        · intro d hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hd
          rcases hd with rfl | rfl | rfl <;> assumption
      rw [hKeq]
      exact tri a b c hab hac hbc (h a ha b hbK hab) (h a ha c hc hac) (h b hbK c hc hbc)
    · rintro ⟨l, hl, m, hm, rfl⟩
      intro t ht u hu htu
      exact (hb t u).2 (back l hl m hm t ht u hu htu)
  refine ⟨p2, ?_⟩
  intro K hK h0
  show K.card - 1 = RHS K
  rcases Nat.lt_or_ge K.card 3 with h3 | h3
  · have h12 : K.card = 1 ∨ K.card = 2 := by omega
    rcases h12 with hc1 | hc2
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc1
      exact one a
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc2
      exact two a b hab ((hb a b).1 (h0 a (by simp) b (by simp) hab))
  · obtain ⟨l, hl, m, hm, rfl⟩ := (p2 K h3).1 h0
    exact three l hl m hm

theorem glue {A B C : Prop} (hA : A) (hBC : A → B ∧ C) : A ∧ B ∧ C :=
  ⟨hA, hBC hA⟩

set_option maxRecDepth 100000 in
theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) := by
  intro L hL
  obtain rfl : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  refine glue ?_ ?_
  · decide +kernel
  · intro h1
    exact core _ h1

end PEqualNP.Outside.L_meta_1566

theorem PEqualNP.Outside.L_meta_1566 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ t u : Fin 13, (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true)) ↔
      (t ≠ u ∧ (t = 0 ∨ u = 0)) ∨ (t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ u ∈ ({1, 5, 11} : Finset (Fin 13))) ∨ (t ∈ ({1, 5, 11} : Finset (Fin 13)) ∧ u ∈ ({4, 10, 12} : Finset (Fin 13)))) ∧
    (∀ K : Finset (Fin 13), 3 ≤ K.card → ((∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) ↔
      ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), K = {0, l, m})) ∧
    (∀ K : Finset (Fin 13), 1 ≤ K.card → (∀ t ∈ K, ∀ u ∈ K, t ≠ u → (t ≠ u ∧ (∃ p ∈ L t \ L u, ∃ v ∈ L u, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L t ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if t ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if t = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (fun v : Fin 13 => decide (v = p ∨ v ∈ (if (0 : Fin 13) ∉ L u ∧ p ≠ 1 then ({0} : Finset (Fin 13)) else if u ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ p ≠ 0 then {1} else if u = 0 ∧ (p = 3 ∨ p = 9) then Finset.univ \ L 0 else ∅))) v = true))) →
      K.card - 1 = (if (0 : Fin 13) ∈ K ∧ 2 ≤ K.card then 1 else 0) +
        (if ∃ l ∈ K, ∃ m ∈ K, l ∈ ({4, 10, 12} : Finset (Fin 13)) ∧ m ∈ ({1, 5, 11} : Finset (Fin 13)) then 1 else 0)) :=
  PEqualNP.Outside.L_meta_1566.main_aux
