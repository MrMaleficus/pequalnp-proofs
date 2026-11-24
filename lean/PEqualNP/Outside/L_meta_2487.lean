import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2487

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem getD_mem (l : List ℕ) (hl : l.length = 2) (c : ℕ) (hc : c < 2) : l.getD c 0 ∈ l := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hl
  have h : c = 0 ∨ c = 1 := by omega
  rcases h with rfl | rfl
  · simp
  · simp

/-- The wire read in a slot: the slot is a pair (gate wire, position). -/
def rd (n : ℕ) (C : Circuit) (s : ℕ × ℕ) : ℕ := (gateAt C (s.1 - n)).inputs.getD s.2 0

/-- The wire is the wire of an AND gate. -/
def isAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop := (gateAt C (w - n)).op = GateOp.and

theorem rd_add (n : ℕ) (C : Circuit) (j c : ℕ) :
    rd n C (n + j, c) = (gateAt C j).inputs.getD c 0 := by
  show (gateAt C (n + j - n)).inputs.getD c 0 = (gateAt C j).inputs.getD c 0
  rw [Nat.add_sub_cancel_left]

theorem isAnd_add (n : ℕ) (C : Circuit) (j : ℕ) :
    isAnd n C (n + j) ↔ (gateAt C j).op = GateOp.and := by
  show (gateAt C (n + j - n)).op = GateOp.and ↔ (gateAt C j).op = GateOp.and
  rw [Nat.add_sub_cancel_left]

theorem card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (R : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b, b ∈ t ∧ R a b)
    (h2 : ∀ a ∈ s, ∀ a' ∈ s, ∀ b, R a b → R a' b → a = a') : s.card ≤ t.card := by
  classical
  have h3 : s.attach.card ≤ t.card := by
    refine Finset.card_le_card_of_injOn (fun a : {x // x ∈ s} => (h1 a.1 a.2).choose) ?_ ?_
    · intro a _
      exact Finset.mem_coe.2 (h1 a.1 a.2).choose_spec.1
    · intro a _ a' _ hEq
      apply Subtype.ext
      have e1 := (h1 a.1 a.2).choose_spec.2
      have e2 := (h1 a'.1 a'.2).choose_spec.2
      have hEq' : (h1 a.1 a.2).choose = (h1 a'.1 a'.2).choose := hEq
      rw [← hEq'] at e2
      exact h2 a.1 a.2 a'.1 a'.2 _ e1 e2
  calc s.card = s.attach.card := Finset.card_attach.symm
    _ ≤ t.card := h3

theorem core (n N : ℕ) (C : Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ)
    (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)) (Wf : Finset ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (H1 : ∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (H2 : ∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length)
    (H3 : ∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧
      (gateAt C j2).op = GateOp.or ∧ (gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧
      seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2))
    (H4 : ∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2)
    (hWf : ∀ x, x ∈ Wf ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) :
    Pl.card ≤ Wf.card + (Pl.image top).card := by
  classical
  obtain ⟨hAO, hRB, hlen2⟩ := hC
  have wide_of : ∀ p ∈ Pl, ∀ x, seg p x → 2 ≤ (D x).card → x ∈ Wf :=
    fun p hp x hs hc => (hWf x).2 ⟨p, hp, hs, hc⟩
  have narrow_of : ∀ p ∈ Pl, ∀ x, seg p x → x ∉ Wf → (D x).card ≤ 1 := by
    intro p hp x hs hx
    by_contra hc
    exact hx (wide_of p hp x hs (by omega))
  have hT : ∀ p ∈ Pl, top p ∈ Pl.image top := fun p hp => Finset.mem_image_of_mem top hp
  -- points with a narrow top inject into the narrow tops
  have hA : (Pl.filter (fun p => ¬ top p ∈ Wf)).card ≤
      ((Pl.image top).filter (fun t => ¬ t ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun p t => top p = t) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      exact ⟨top p, Finset.mem_filter.2 ⟨hT p hp.1, hp.2⟩, rfl⟩
    · intro p hp q hq t hpt hqt
      rw [Finset.mem_filter] at hp hq
      have hsp := (H1 p hp.1).2.1
      have hsq := (H1 q hq.1).2.1
      have hc := narrow_of p hp.1 (top p) hsp hp.2
      have hpD := (H2 p hp.1 (top p) hsp).1
      have hqD := (H2 q hq.1 (top q) hsq).1
      have hpt' : top p = t := hpt
      have hqt' : top q = t := hqt
      have e : top q = top p := hqt'.trans hpt'.symm
      rw [e] at hqD
      exact Finset.card_le_one.1 hc p hpD q hqD
  -- wide wires that are not tops inject into the slots reading a wide wire
  have hB : (Wf.filter (fun w => ¬ w ∈ Pl.image top)).card ≤
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => rd n C s ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun w s => rd n C s = w) ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨p, hp, hs, hc⟩ := (hWf w).1 hw.1
      have hne : w ≠ top p := by
        intro e
        apply hw.2
        rw [e]
        exact hT p hp
      obtain ⟨j2, c, hj2, hop, hrd, hc2, hseg, hsub⟩ := H3 p hp w hs hne
      have hwide : n + j2 ∈ Wf :=
        wide_of p hp _ hseg (le_trans hc (Finset.card_le_card hsub))
      refine ⟨(n + j2, c), Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨hwide, ?_⟩, Finset.mem_range.2 hc2⟩, ?_⟩, ?_⟩
      · show ¬ isAnd n C (n + j2)
        rw [isAnd_add, hop]
        intro hh
        cases hh
      · show rd n C (n + j2, c) ∈ Wf
        rw [rd_add, hrd]
        exact hw.1
      · show rd n C (n + j2, c) = w
        rw [rd_add]
        exact hrd
    · intro w _ w' _ s h1 h2
      have h1' : rd n C s = w := h1
      have h2' : rd n C s = w' := h2
      exact h1'.symm.trans h2'
  -- points with a wide top and a narrow source inject into the slots reading a narrow wire
  have hBii : (Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)).card ≤
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ rd n C s ∈ Wf)).card := by
    refine card_le_of_rel _ _ (fun p s => p ∈ D (rd n C s) ∧ (D (rd n C s)).card ≤ 1) ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpP, htop, hsrc⟩ := hp
      have step : ∀ m x, n + C.gates.length - x < m → seg p x → ¬ x ∈ Wf →
          ∃ s, s ∈ ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
              (fun s => ¬ rd n C s ∈ Wf) ∧
            (p ∈ D (rd n C s) ∧ (D (rd n C s)).card ≤ 1) := by
        intro m
        induction m with
        | zero =>
          intro x hx
          exact absurd hx (Nat.not_lt_zero _)
        | succ m ih =>
          intro x hx hs hxW
          have hne : x ≠ top p := by
            intro e
            rw [e] at hxW
            exact hxW htop
          obtain ⟨j2, c, hj2, hop, hrd, hc2, hseg, hsub⟩ := H3 p hpP x hs hne
          have hmem : x ∈ (gateAt C j2).inputs := by
            rw [← hrd]
            exact getD_mem _ (hlen2 _ (gate_mem C j2 hj2)) c hc2
          have hlt : x < n + j2 := hRB j2 hj2 x hmem
          by_cases hw : n + j2 ∈ Wf
          · refine ⟨(n + j2, c), Finset.mem_filter.2 ⟨Finset.mem_product.2
              ⟨Finset.mem_filter.2 ⟨hw, ?_⟩, Finset.mem_range.2 hc2⟩, ?_⟩, ?_, ?_⟩
            · show ¬ isAnd n C (n + j2)
              rw [isAnd_add, hop]
              intro hh
              cases hh
            · show ¬ rd n C (n + j2, c) ∈ Wf
              rw [rd_add, hrd]
              exact hxW
            · show p ∈ D (rd n C (n + j2, c))
              rw [rd_add, hrd]
              exact (H2 p hpP x hs).1
            · show (D (rd n C (n + j2, c))).card ≤ 1
              rw [rd_add, hrd]
              exact narrow_of p hpP x hs hxW
          · exact ih (n + j2) (by omega) hseg hw
      exact step _ (src p) (Nat.lt_succ_self _) (H1 p hpP).1 hsrc
    · intro p _ q _ s h1 h2
      exact Finset.card_le_one.1 h1.2 p h1.1 q h2.1
  -- points with a wide source: at most two for each wide AND wire
  have hBi : (Pl.filter (fun p => src p ∈ Wf)).card ≤
      2 * (Wf.filter (fun w => isAnd n C w)).card := by
    refine le_trans (Finset.card_le_mul_card_image (f := src)
      (Pl.filter (fun p => src p ∈ Wf)) 2 ?_) ?_
    · intro g _
      refine le_trans (Finset.card_le_card ?_) (H4 g)
      intro q hq
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨(Finset.mem_filter.1 hq.1).1, hq.2⟩
    · refine Nat.mul_le_mul_left 2 (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hw
      rw [Finset.mem_filter] at hp
      obtain ⟨j, hj, _, hop⟩ := (H1 p hp.1).2.2
      refine Finset.mem_filter.2 ⟨hp.2, ?_⟩
      show isAnd n C (src p)
      rw [hj, isAnd_add]
      exact hop
  have hcov : Pl.card ≤ (Pl.filter (fun p => ¬ top p ∈ Wf)).card +
      (Pl.filter (fun p => src p ∈ Wf)).card +
      (Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)).card := by
    refine le_trans (Finset.card_le_card (t := (Pl.filter (fun p => ¬ top p ∈ Wf) ∪
      Pl.filter (fun p => src p ∈ Wf)) ∪
      Pl.filter (fun p => top p ∈ Wf ∧ ¬ src p ∈ Wf)) ?_) ?_
    · intro p hp
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
        Finset.mem_filter]
      by_cases h1 : top p ∈ Wf
      · by_cases h2 : src p ∈ Wf
        · exact Or.inl (Or.inr ⟨hp, h2⟩)
        · exact Or.inr ⟨hp, h1, h2⟩
      · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · exact le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have e1 : (Wf.filter (fun w => isAnd n C w)).card +
      (Wf.filter (fun w => ¬ isAnd n C w)).card = Wf.card :=
    Finset.card_filter_add_card_filter_not _
  have e2 : (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => rd n C s ∈ Wf)).card +
      (((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).filter
        (fun s => ¬ rd n C s ∈ Wf)).card =
      ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).card :=
    Finset.card_filter_add_card_filter_not _
  have e3 : ((Wf.filter (fun w => ¬ isAnd n C w)) ×ˢ Finset.range 2).card =
      (Wf.filter (fun w => ¬ isAnd n C w)).card * 2 := by
    rw [Finset.card_product, Finset.card_range]
  have e4 : (Wf.filter (fun w => w ∈ Pl.image top)).card +
      (Wf.filter (fun w => ¬ w ∈ Pl.image top)).card = Wf.card :=
    Finset.card_filter_add_card_filter_not _
  have e5 : ((Pl.image top).filter (fun t => t ∈ Wf)).card +
      ((Pl.image top).filter (fun t => ¬ t ∈ Wf)).card = (Pl.image top).card :=
    Finset.card_filter_add_card_filter_not _
  have e6 : (Wf.filter (fun w => w ∈ Pl.image top)).card ≤
      ((Pl.image top).filter (fun t => t ∈ Wf)).card := by
    refine Finset.card_le_card ?_
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.2, hw.1⟩
  omega

theorem main_aux : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card := by
  classical
  intro n N C Pl src top seg D hC H1 H2 H3 H4
  have hfin : ∀ x, x ∈ (Finset.range (n + C.gates.length)).filter
      (fun x => ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card) ↔ ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card := by
    intro x
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · rintro ⟨p, hp, hs, hc⟩
      exact ⟨(H2 p hp x hs).2.2, p, hp, hs, hc⟩
  have hEq : {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card} =
      (↑((Finset.range (n + C.gates.length)).filter
        (fun x => ∃ p ∈ Pl, seg p x ∧ 2 ≤ (D x).card)) : Set ℕ) := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_coe.2 ((hfin x).2 hx)
    · intro hx
      exact (hfin x).1 (Finset.mem_coe.1 hx)
  rw [hEq, Set.ncard_coe_finset]
  exact core n N C Pl src top seg D _ hC H1 H2 H3 H4 hfin

end PEqualNP.Outside.L_meta_2487

theorem PEqualNP.Outside.L_meta_2487 : ∀ (n N : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (Pl : Finset (Fin N)) (src top : Fin N → ℕ) (seg : Fin N → ℕ → Prop) (D : ℕ → Finset (Fin N)), PEqualNP.TopForm.IsAO2 n C → (∀ p ∈ Pl, seg p (src p) ∧ seg p (top p) ∧ ∃ j, src p = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ p2 ∈ Pl, ∀ x : ℕ, seg p2 x → p2 ∈ D x ∧ n ≤ x ∧ x < n + C.gates.length) → (∀ p3 ∈ Pl, ∀ x2 : ℕ, seg p3 x2 → x2 ≠ top p3 → ∃ j2 c, j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs.getD c 0 = x2 ∧ c < 2 ∧ seg p3 (n + j2) ∧ D x2 ⊆ D (n + j2)) → (∀ g : ℕ, (Pl.filter (fun p4 => src p4 = g)).card ≤ 2) → Pl.card ≤ {x3 : ℕ | ∃ p5 ∈ Pl, seg p5 x3 ∧ 2 ≤ (D x3).card}.ncard + (Pl.image top).card :=
  PEqualNP.Outside.L_meta_2487.main_aux
