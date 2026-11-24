import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2405

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

abbrev RR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (Stp n C)

abbrev InL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (w : ℕ) (x : α) : Prop :=
  ∃ m ∈ labelled, RR n C m w ∧ x ∈ lab m

abbrev DOK (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (W : Finset ℕ) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ (∃ w ∈ W, RR n C (n + j) w) ∧
    (∃ x, InL n C labelled lab ((gateAt C j).inputs.getD 0 0) x) ∧
    (∃ y, InL n C labelled lab ((gateAt C j).inputs.getD 1 0) y) ∧
    ∀ z, InL n C labelled lab ((gateAt C j).inputs.getD 0 0) z →
      ¬ InL n C labelled lab ((gateAt C j).inputs.getD 1 0) z

abbrev TOK (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (W : Finset ℕ) (m : ℕ) : Prop :=
  m ∈ labelled ∧ (lab m).card = 2 ∧ ∃ w ∈ W, RR n C m w

abbrev Inv (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (W : Finset ℕ) : Prop :=
  ∃ (c : α → α) (D T : Finset ℕ),
    (∀ w ∈ W, ∀ x y, InL n C labelled lab w x → InL n C labelled lab w y → c x = c y) ∧
    (∀ j ∈ D, DOK n C labelled lab W j) ∧
    (∀ m ∈ T, TOK n C labelled lab W m) ∧
    ∀ U : Finset α, ∃ U2 : Finset α, U2 ⊆ U ∧ (∀ x ∈ U2, ∀ y ∈ U2, c x = c y → x = y) ∧
      U.card ≤ U2.card + D.card + T.card

theorem R_le {n : ℕ} {C : Circuit} {u v : ℕ} (h : RR n C u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt hs.1)

theorem R_cases {n : ℕ} {C : Circuit} {u v : ℕ} (h : RR n C u v) :
    u = v ∨ ∃ a, RR n C u a ∧ Stp n C a v := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨a, h1, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr ⟨a, h1, h2⟩

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem merge {α : Type} (c : α → α) (p q : α) :
    ∃ c2 : α → α, c2 p = c2 q ∧ (∀ u v, c u = c v → c2 u = c2 v) ∧
      ∀ U1 : Finset α, (∀ x ∈ U1, ∀ y ∈ U1, c x = c y → x = y) →
        ∃ U2 : Finset α, U2 ⊆ U1 ∧ (∀ x ∈ U2, ∀ y ∈ U2, c2 x = c2 y → x = y) ∧
          U1.card ≤ U2.card + 1 := by
  classical
  refine ⟨fun u => if c u = c q then c p else c u, ?_, ?_, ?_⟩
  · simp
  · intro u v h
    simp only [h]
  · intro U1 hinj
    by_cases hex : ∃ z ∈ U1, c z = c q
    · obtain ⟨z, hz, hzq⟩ := hex
      refine ⟨U1.erase z, Finset.erase_subset z U1, ?_, ?_⟩
      · intro x hx y hy hxy
        have hx1 := Finset.mem_of_mem_erase hx
        have hy1 := Finset.mem_of_mem_erase hy
        have hxq : ¬ c x = c q := fun h =>
          Finset.ne_of_mem_erase hx (hinj x hx1 z hz (h.trans hzq.symm))
        have hyq : ¬ c y = c q := fun h =>
          Finset.ne_of_mem_erase hy (hinj y hy1 z hz (h.trans hzq.symm))
        simp only [if_neg hxq, if_neg hyq] at hxy
        exact hinj x hx1 y hy1 hxy
      · rw [Finset.card_erase_of_mem hz]
        have := Finset.card_pos.mpr ⟨z, hz⟩
        omega
    · refine ⟨U1, Finset.Subset.refl U1, ?_, Nat.le_succ _⟩
      intro x hx y hy hxy
      have hxq : ¬ c x = c q := fun h => hex ⟨x, hx, h⟩
      have hyq : ¬ c y = c q := fun h => hex ⟨y, hy, h⟩
      simp only [if_neg hxq, if_neg hyq] at hxy
      exact hinj x hx y hy hxy

theorem DOK_lift (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    {W1 W : Finset ℕ}
    (hsub : ∀ w ∈ W1, ∃ w2 ∈ W, ∀ u, RR n C u w → RR n C u w2) {j : ℕ}
    (h : DOK n C labelled lab W1 j) : DOK n C labelled lab W j := by
  obtain ⟨e1, e2, ⟨w, hw, hR⟩, e4⟩ := h
  obtain ⟨w2, hw2, hl⟩ := hsub w hw
  exact ⟨e1, e2, ⟨w2, hw2, hl _ hR⟩, e4⟩

theorem TOK_lift (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    {W1 W : Finset ℕ}
    (hsub : ∀ w ∈ W1, ∃ w2 ∈ W, ∀ u, RR n C u w → RR n C u w2) {m : ℕ}
    (h : TOK n C labelled lab W1 m) : TOK n C labelled lab W m := by
  obtain ⟨e1, e2, w, hw, hR⟩ := h
  obtain ⟨w2, hw2, hl⟩ := hsub w hw
  exact ⟨e1, e2, w2, hw2, hl _ hR⟩

theorem step_plain (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (W1 W : Finset ℕ) (k : ℕ)
    (hsub : ∀ w ∈ W1, ∃ w2 ∈ W, ∀ u, RR n C u w → RR n C u w2)
    (hrest : ∀ w ∈ W, w ≠ k → w ∈ W1)
    (hI : Inv n C labelled lab W1)
    (hconst : ∀ c : α → α,
      (∀ w ∈ W1, ∀ x y, InL n C labelled lab w x → InL n C labelled lab w y → c x = c y) →
      ∀ x y, InL n C labelled lab k x → InL n C labelled lab k y → c x = c y) :
    Inv n C labelled lab W := by
  obtain ⟨c, D, T, h1, h2, h3, h4⟩ := hI
  refine ⟨c, D, T, ?_, fun j hj => DOK_lift n C labelled lab hsub (h2 j hj),
    fun m hm => TOK_lift n C labelled lab hsub (h3 m hm), h4⟩
  intro w hw x y hx hy
  by_cases hwk : w = k
  · rw [hwk] at hx hy
    exact hconst c h1 x y hx hy
  · exact h1 w (hrest w hw hwk) x y hx hy

theorem step_merge (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (W1 W : Finset ℕ) (k : ℕ)
    (hrest : ∀ w ∈ W, w ≠ k → w ∈ W1)
    (c1 : α → α) (D1 T1 D T : Finset ℕ)
    (h1 : ∀ w ∈ W1, ∀ x y, InL n C labelled lab w x → InL n C labelled lab w y → c1 x = c1 y)
    (h4 : ∀ U : Finset α, ∃ U2 : Finset α, U2 ⊆ U ∧
      (∀ x ∈ U2, ∀ y ∈ U2, c1 x = c1 y → x = y) ∧ U.card ≤ U2.card + D1.card + T1.card)
    (hD : ∀ j ∈ D, DOK n C labelled lab W j)
    (hT : ∀ m ∈ T, TOK n C labelled lab W m)
    (hcard : D1.card + T1.card + 1 ≤ D.card + T.card)
    (p q : α)
    (hconst : ∀ c : α → α,
      (∀ w ∈ W1, ∀ x y, InL n C labelled lab w x → InL n C labelled lab w y → c x = c y) →
      c p = c q →
      ∀ x y, InL n C labelled lab k x → InL n C labelled lab k y → c x = c y) :
    Inv n C labelled lab W := by
  obtain ⟨c, hpq, hmono, hU⟩ := merge c1 p q
  have h1c : ∀ w ∈ W1, ∀ x y, InL n C labelled lab w x → InL n C labelled lab w y →
      c x = c y := fun w hw x y hx hy => hmono _ _ (h1 w hw x y hx hy)
  refine ⟨c, D, T, ?_, hD, hT, ?_⟩
  · intro w hw x y hx hy
    by_cases hwk : w = k
    · rw [hwk] at hx hy
      exact hconst c h1c hpq x y hx hy
    · exact h1c w (hrest w hw hwk) x y hx hy
  · intro U
    obtain ⟨U1, hs1, hi1, hc1⟩ := h4 U
    obtain ⟨U2, hs2, hi2, hc2⟩ := hU U1 hi1
    exact ⟨U2, hs2.trans hs1, hi2, by omega⟩

theorem inv_all (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (∀ w ∈ W, w < k) → Inv n C labelled lab W := by
  classical
  intro k
  induction k with
  | zero =>
    intro W hW
    refine ⟨id, ∅, ∅, fun w hw => absurd (hW w hw) (Nat.not_lt_zero w), ?_, ?_, ?_⟩
    · intro j hj
      simp at hj
    · intro m hm
      simp at hm
    · intro U
      exact ⟨U, Finset.Subset.refl U, fun x _ y _ h => h, by simp⟩
  | succ k ih =>
    intro W hW
    by_cases hk : k ∈ W
    swap
    · exact ih W (fun w hw => lt_of_le_of_ne (Nat.lt_succ_iff.mp (hW w hw))
        (fun h => hk (h ▸ hw)))
    have hW0 : ∀ w ∈ W.erase k, w < k := fun w hw =>
      lt_of_le_of_ne (Nat.lt_succ_iff.mp (hW w (Finset.mem_of_mem_erase hw)))
        (Finset.ne_of_mem_erase hw)
    by_cases hor : ∃ j, k = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or
    · obtain ⟨j, hkj, hj, hop⟩ := hor
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
      have ha0 : (gateAt C j).inputs.getD 0 0 = a := by simp [hab]
      have hb0 : (gateAt C j).inputs.getD 1 0 = b := by simp [hab]
      have hain : a ∈ (gateAt C j).inputs := by rw [hab]; simp
      have hbin : b ∈ (gateAt C j).inputs := by rw [hab]; simp
      have hak : a < k := by rw [hkj]; exact hAO.2.1 j hj a hain
      have hbk : b < k := by rw [hkj]; exact hAO.2.1 j hj b hbin
      have hRa : RR n C a k := Relation.ReflTransGen.single ⟨hak, j, hkj, hj, hop, hain⟩
      have hRb : RR n C b k := Relation.ReflTransGen.single ⟨hbk, j, hkj, hj, hop, hbin⟩
      have hRjk : RR n C (n + j) k :=
        Eq.mp (congrArg (fun t => RR n C t k) hkj) Relation.ReflTransGen.refl
      have hdec : ∀ u, RR n C u k → u = k ∨ RR n C u a ∨ RR n C u b := by
        intro u hu
        rcases R_cases hu with h | ⟨a2, h1, h2, rj, e1, e2, e3, e4⟩
        · exact Or.inl h
        · have hrj : rj = j := by omega
          rw [hrj, hab] at e4
          rcases List.mem_cons.mp e4 with h3 | h3
          · rw [h3] at h1
            exact Or.inr (Or.inl h1)
          · rw [List.mem_singleton.mp h3] at h1
            exact Or.inr (Or.inr h1)
      have hLk : ∀ x, InL n C labelled lab k x →
          InL n C labelled lab a x ∨ InL n C labelled lab b x := by
        intro x hxk
        obtain ⟨m, hm, hR, hx⟩ := hxk
        rcases hdec m hR with h | h | h
        · exfalso
          rcases (hlab m hm).1 with h1 | ⟨j2, e1, e2, e3⟩
          · omega
          · have hj2 : j2 = j := by omega
            rw [hj2, hop] at e3
            cases e3
        · exact Or.inl ⟨m, hm, h, hx⟩
        · exact Or.inr ⟨m, hm, h, hx⟩
      have hW1 : ∀ w ∈ insert a (insert b (W.erase k)), w < k := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_insert] at hw
        rcases hw with h | h | h
        · rw [h]; exact hak
        · rw [h]; exact hbk
        · exact hW0 w h
      have hsub : ∀ w ∈ insert a (insert b (W.erase k)),
          ∃ w2 ∈ W, ∀ u, RR n C u w → RR n C u w2 := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_insert] at hw
        rcases hw with h | h | h
        · rw [h]; exact ⟨k, hk, fun u hu => hu.trans hRa⟩
        · rw [h]; exact ⟨k, hk, fun u hu => hu.trans hRb⟩
        · exact ⟨w, Finset.mem_of_mem_erase h, fun u hu => hu⟩
      have hrest : ∀ w ∈ W, w ≠ k → w ∈ insert a (insert b (W.erase k)) :=
        fun w hw hwk => Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwk, hw⟩))
      have hIW := ih _ hW1
      by_cases hdm : (∃ x, InL n C labelled lab a x) ∧ (∃ y, InL n C labelled lab b y) ∧
          ∀ z, InL n C labelled lab a z → ¬ InL n C labelled lab b z
      · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, hdis⟩ := hdm
        obtain ⟨c1, D1, T1, h1, h2, h3, h4⟩ := hIW
        have hjD : j ∉ D1 := by
          intro hjm
          obtain ⟨-, -, ⟨w, hw, hR⟩, -⟩ := h2 j hjm
          have hle := R_le hR
          have hlt := hW1 w hw
          omega
        refine step_merge n C labelled lab _ W k hrest c1 D1 T1 (insert j D1) T1 h1 h4 ?_
          (fun m hm => TOK_lift n C labelled lab hsub (h3 m hm)) ?_ p q ?_
        · intro j2 hj2
          rw [Finset.mem_insert] at hj2
          rcases hj2 with hj2e | hj2
          · rw [hj2e]
            refine ⟨hj, hop, ⟨k, hk, hRjk⟩, ?_, ?_, ?_⟩
            · rw [ha0]; exact ⟨p, hp⟩
            · rw [hb0]; exact ⟨q, hq⟩
            · rw [ha0, hb0]; exact hdis
          · exact DOK_lift n C labelled lab hsub (h2 j2 hj2)
        · rw [Finset.card_insert_of_notMem hjD]
          omega
        · intro c hc hpq x y hx hy
          have key : ∀ z, InL n C labelled lab k z → c z = c p := by
            intro z hz
            rcases hLk z hz with h | h
            · exact hc a (Finset.mem_insert_self _ _) z p h hp
            · exact (hc b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                z q h hq).trans hpq.symm
          exact (key x hx).trans (key y hy).symm
      · refine step_plain n C labelled lab _ W k hsub hrest hIW ?_
        intro c hc x y hx hy
        have hca := hc a (Finset.mem_insert_self _ _)
        have hcb := hc b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
        rcases hLk x hx with h | h <;> rcases hLk y hy with h' | h'
        · exact hca x y h h'
        · by_contra hne
          apply hdm
          refine ⟨⟨x, h⟩, ⟨y, h'⟩, fun z hza hzb => hne ?_⟩
          exact (hca x z h hza).trans (hcb z y hzb h')
        · by_contra hne
          apply hdm
          refine ⟨⟨y, h'⟩, ⟨x, h⟩, fun z hza hzb => hne ?_⟩
          exact (hcb x z h hzb).trans (hca z y hza h')
        · exact hcb x y h h'
    · have hleaf : ∀ u, RR n C u k → u = k := by
        intro u hu
        rcases R_cases hu with h | ⟨a2, -, -, rj, e1, e2, e3, -⟩
        · exact h
        · exact absurd ⟨rj, e1, e2, e3⟩ hor
      have hsub : ∀ w ∈ W.erase k, ∃ w2 ∈ W, ∀ u, RR n C u w → RR n C u w2 :=
        fun w hw => ⟨w, Finset.mem_of_mem_erase hw, fun u hu => hu⟩
      have hrest : ∀ w ∈ W, w ≠ k → w ∈ W.erase k :=
        fun w hw hwk => Finset.mem_erase.mpr ⟨hwk, hw⟩
      have hIW := ih _ hW0
      have hLk : ∀ x, InL n C labelled lab k x → k ∈ labelled ∧ x ∈ lab k := by
        intro x hxk
        obtain ⟨m, hm, hR, hx⟩ := hxk
        have hmk := hleaf m hR
        rw [hmk] at hm hx
        exact ⟨hm, hx⟩
      by_cases h2l : k ∈ labelled ∧ (lab k).card = 2
      · obtain ⟨p, q, hpq_ne, hlabk⟩ := Finset.card_eq_two.mp h2l.2
        obtain ⟨c1, D1, T1, h1, h2, h3, h4⟩ := hIW
        have hkT : k ∉ T1 := by
          intro hkm
          obtain ⟨-, -, w, hw, hR⟩ := h3 k hkm
          have hle := R_le hR
          have hlt := hW0 w hw
          omega
        refine step_merge n C labelled lab _ W k hrest c1 D1 T1 D1 (insert k T1) h1 h4
          (fun j hj => DOK_lift n C labelled lab hsub (h2 j hj)) ?_ ?_ p q ?_
        · intro m hm
          rw [Finset.mem_insert] at hm
          rcases hm with hmk | hm
          · rw [hmk]
            exact ⟨h2l.1, h2l.2, k, hk, Relation.ReflTransGen.refl⟩
          · exact TOK_lift n C labelled lab hsub (h3 m hm)
        · rw [Finset.card_insert_of_notMem hkT]
          omega
        · intro c hc hpq x y hx hy
          have key : ∀ z, InL n C labelled lab k z → c z = c p := by
            intro z hz
            have hz2 := (hLk z hz).2
            rw [hlabk, Finset.mem_insert, Finset.mem_singleton] at hz2
            rcases hz2 with h | h
            · exact congrArg c h
            · exact (congrArg c h).trans hpq.symm
          exact (key x hx).trans (key y hy).symm
      · refine step_plain n C labelled lab _ W k hsub hrest hIW ?_
        intro c hc x y hx hy
        obtain ⟨hkl, hxk⟩ := hLk x hx
        obtain ⟨-, hyk⟩ := hLk y hy
        have hc1 : (lab k).card ≤ 1 := by
          have hle2 := (hlab k hkl).2
          have hne2 : (lab k).card ≠ 2 := fun h => h2l ⟨hkl, h⟩
          omega
        exact congrArg c (Finset.card_le_one.mp hc1 x hxk y hyk)

theorem card_le_ncard {β : Type} (D : Finset β) (s : Set β) (hfin : s.Finite)
    (h : ∀ j ∈ D, j ∈ s) : D.card ≤ s.ncard := by
  rw [← Set.ncard_coe_finset D]
  exact Set.ncard_le_ncard (fun j hj => h j hj) hfin

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ roots.card + {jm : ℕ | jm < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jm).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jm) r2) ∧ ({x3 : α | ∃ m3 ∈ labelled, R m3 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x3 ∈ lab m3}).Nonempty ∧ ({x4 : α | ∃ m4 ∈ labelled, R m4 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x4 ∈ lab m4}).Nonempty ∧ Disjoint {x5 : α | ∃ m5 ∈ labelled, R m5 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x5 ∈ lab m5} {x6 : α | ∃ m6 ∈ labelled, R m6 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x6 ∈ lab m6}}.ncard + {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard := by
  intro n C α S roots labelled lab hAO R hR hlab hS
  subst hR
  classical
  obtain ⟨c, D, T, h1, h2, h3, h4⟩ := inv_all n C labelled lab hAO hlab (roots.sup id + 1) roots
    (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
  obtain ⟨U2, hsub, hinj, hcard⟩ := h4 S
  have hU2 : U2.card ≤ roots.card := by
    choose! f hf using hS
    refine Finset.card_le_card_of_injOn f (fun x hx => (hf x (hsub hx)).1) ?_
    intro x hx y hy hxy
    obtain ⟨hr, m1, hm1, hR1, hx1⟩ := hf x (hsub hx)
    obtain ⟨-, m2, hm2, hR2, hy1⟩ := hf y (hsub hy)
    rw [← hxy] at hR2
    exact hinj x hx y hy (h1 (f x) hr x y ⟨m1, hm1, hR1, hx1⟩ ⟨m2, hm2, hR2, hy1⟩)
  refine le_trans hcard (Nat.add_le_add (Nat.add_le_add hU2 ?_) ?_)
  · refine card_le_ncard D _ ((Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)) ?_
    intro j hj
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h2 j hj
    exact ⟨e1, e2, e3, e4, e5, Set.disjoint_left.mpr (fun z hz1 hz2 => e6 z hz1 hz2)⟩
  · refine card_le_ncard T _ (labelled.finite_toSet.subset (fun m hm => hm.1)) ?_
    intro m hm
    exact ⟨(h3 m hm).1, (h3 m hm).2.1⟩

end PEqualNP.Outside.L_meta_2405

theorem PEqualNP.Outside.L_meta_2405 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ roots.card + {jm : ℕ | jm < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jm).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jm) r2) ∧ ({x3 : α | ∃ m3 ∈ labelled, R m3 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x3 ∈ lab m3}).Nonempty ∧ ({x4 : α | ∃ m4 ∈ labelled, R m4 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x4 ∈ lab m4}).Nonempty ∧ Disjoint {x5 : α | ∃ m5 ∈ labelled, R m5 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x5 ∈ lab m5} {x6 : α | ∃ m6 ∈ labelled, R m6 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x6 ∈ lab m6}}.ncard + {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard :=
  PEqualNP.Outside.L_meta_2405.main_aux
