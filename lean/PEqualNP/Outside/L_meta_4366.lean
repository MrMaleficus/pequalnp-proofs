import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4366

theorem descent {α : Type} (sz cnt : α → ℕ) (Good : α → Prop) (R : α → α → Prop)
    (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hsz : ∀ a b, R a b → sz a ≤ sz b)
    (step : ∀ a, Good a → cnt a ≠ 0 → ∃ b, Good b ∧ R b a ∧ (sz b < sz a ∨ cnt b < cnt a)) :
    ∀ a, Good a → ∃ b, Good b ∧ R b a ∧ cnt b = 0 := by
  suffices H : ∀ s c a, sz a = s → cnt a = c → Good a → ∃ b, Good b ∧ R b a ∧ cnt b = 0 from
    fun a => H _ _ a rfl rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ihs =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro a hs hc ha
  by_cases h0 : cnt a = 0
  · exact ⟨a, ha, hrefl a, h0⟩
  · obtain ⟨b, hb, hba, hlt⟩ := step a ha h0
    have hle := hsz b a hba
    have key : ∃ d, Good d ∧ R d b ∧ cnt d = 0 := by
      rcases Nat.lt_or_ge (sz b) (sz a) with h1 | h1
      · exact ihs (sz b) (by omega) (cnt b) b rfl rfl hb
      · rcases hlt with hlt | hlt
        · omega
        · exact ihc (cnt b) (by omega) b (by omega) rfl hb
    obtain ⟨d, hd, hdb, hd0⟩ := key
    exact ⟨d, hd, htrans d b a hdb hba, hd0⟩

theorem main_aux : (∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
        ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
    PEqualNP.TopForm.IsAO2 (p + l) C →
    (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
    Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), (i : ℕ) < p) ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), p ≤ (i : ℕ))} ≠ 0 →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (p + l) C' ∧ C'.size ≤ C.size ∧
      C'.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ≤
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ∧
      PEqualNP.MetaComplexity.circuitFun (p + l) C' = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧
      (C'.size < C.size ∨
       Set.ncard {j : ℕ | j < C'.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), (i : ℕ) < p) ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), p ≤ (i : ℕ))} <
        Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), (i : ℕ) < p) ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), p ≤ (i : ℕ))})) →
∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (p + l) C →
  (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (p + l) C' ∧
    C'.size ≤ C.size ∧
    C'.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ≤
      C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ∧
    PEqualNP.MetaComplexity.circuitFun (p + l) C' = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧
    ∀ j < C'.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ¬ ((∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), (i : ℕ) < p) ∧
         (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), p ≤ (i : ℕ))) := by
  intro H p l E C hE hC hF
  have := descent (α := PEqualNP.CircuitLowerBounds.Circuit)
    (fun C => C.size)
    (fun C => Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), (i : ℕ) < p) ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), p ≤ (i : ℕ))})
    (fun C => PEqualNP.TopForm.IsAO2 (p + l) C ∧ (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)))
    (fun C' C => C'.size ≤ C.size ∧
      C'.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ≤
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ∧
      PEqualNP.MetaComplexity.circuitFun (p + l) C' = PEqualNP.MetaComplexity.circuitFun (p + l) C)
    (fun a => ⟨le_refl _, le_refl _, rfl⟩)
    (fun a b c hab hbc => ⟨le_trans hab.1 hbc.1, le_trans hab.2.1 hbc.2.1, hab.2.2.trans hbc.2.2⟩)
    (fun a b hab => hab.1)
    (by
      intro a ha h0
      obtain ⟨b, hb1, hsz, hcnt, hfun, hlt⟩ := H p l E a hE ha.1 ha.2 h0
      exact ⟨b, ⟨hb1, fun x => by rw [hfun]; exact ha.2 x⟩, ⟨hsz, hcnt, hfun⟩, hlt⟩)
    C ⟨hC, hF⟩
  obtain ⟨b, ⟨hb1, _⟩, ⟨hsz, hcnt, hfun⟩, hb0⟩ := this
  refine ⟨b, hb1, hsz, hcnt, hfun, ?_⟩
  intro j hj hor hmix
  have hfin : Set.Finite {j : ℕ | j < b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt b j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) b (p + l + j), (i : ℕ) < p) ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) b (p + l + j), p ≤ (i : ℕ))} :=
    (Set.finite_Iio b.gates.length).subset (fun k hk => Set.mem_Iio.mpr hk.1)
  have hempty := (Set.ncard_eq_zero hfin).mp hb0
  have hmem : j ∈ {j : ℕ | j < b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt b j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) b (p + l + j), (i : ℕ) < p) ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) b (p + l + j), p ≤ (i : ℕ))} := ⟨hj, hor, hmix.1, hmix.2⟩
  rw [hempty] at hmem
  exact hmem

end PEqualNP.Outside.L_meta_4366

theorem PEqualNP.Outside.L_meta_4366 : (∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
        ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
    PEqualNP.TopForm.IsAO2 (p + l) C →
    (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
    Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), (i : ℕ) < p) ∧
        (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), p ≤ (i : ℕ))} ≠ 0 →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (p + l) C' ∧ C'.size ≤ C.size ∧
      C'.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ≤
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ∧
      PEqualNP.MetaComplexity.circuitFun (p + l) C' = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧
      (C'.size < C.size ∨
       Set.ncard {j : ℕ | j < C'.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), (i : ℕ) < p) ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), p ≤ (i : ℕ))} <
        Set.ncard {j : ℕ | j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), (i : ℕ) < p) ∧
          (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C (p + l + j), p ≤ (i : ℕ))})) →
∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
  PEqualNP.TopForm.IsAO2 (p + l) C →
  (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) →
  ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 (p + l) C' ∧
    C'.size ≤ C.size ∧
    C'.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ≤
      C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec true false false (fun _ => false) false g.op) ∧
    PEqualNP.MetaComplexity.circuitFun (p + l) C' = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧
    ∀ j < C'.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      ¬ ((∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), (i : ℕ) < p) ∧
         (∃ i ∈ PEqualNP.TopForm.orIn (p + l) C' (p + l + j), p ≤ (i : ℕ))) :=
  PEqualNP.Outside.L_meta_4366.main_aux
