import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2409

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- One upward step along an OR gate. -/
def stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The pairs having a wire above the point whose shadow has two points, all on the line. -/
def Bp (N M : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop) (R : ℕ → ℕ → Prop)
    (ex : Fin N × Fin M) : Prop :=
  ∃ w, R (pw ex.1) w ∧ (∀ q : Fin N, R (pw q) w → I q ex.2) ∧
    2 ≤ {r : Fin N | R (pw r) w}.ncard

theorem gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem base (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ) (hpw : Function.Injective pw)
    (hpn : ∀ p2 : Fin N, pw p2 < n) (r p : Fin N)
    (h : Relation.ReflTransGen (stp n C) (pw r) (pw p)) : r = p := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨b, _, hs⟩
  · exact (hpw h1).symm
  · obtain ⟨_, rj, hrj, _⟩ := hs
    have := hpn p
    omega

theorem key (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpw : Function.Injective pw) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (R : ℕ → ℕ → Prop) (hR : R = Relation.ReflTransGen (stp n C))
    (p : Fin N) (w : ℕ) (hw : R (pw p) w) (h2 : 2 ≤ {r : Fin N | R (pw r) w}.ncard) :
    ∃ jo, jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or ∧ (∀ x, R x (n + jo) → R x w) ∧
      2 ≤ {r : Fin N | R (pw r) (n + jo)}.ncard ∧
      ∃ i : Fin 2, R (pw p) ((gateAt C jo).inputs.getD i.val 0) ∧
        ∀ q : Fin N, R (pw q) ((gateAt C jo).inputs.getD i.val 0) → q = p := by
  subst hR
  revert h2
  induction hw with
  | refl =>
    intro h2
    exfalso
    obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2
    have e1 : a = p := base n N C pw hpw hpn a p ha
    have e2 : b = p := base n N C pw hpw hpn b p hb
    exact hab (e1.trans e2.symm)
  | @tail b c hab hbc ih =>
    intro h2
    by_cases hb : 2 ≤ {r : Fin N | Relation.ReflTransGen (stp n C) (pw r) b}.ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih hb
      exact ⟨jo, h1, h3, fun x hx => (h4 x hx).tail hbc, h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hm : gateAt C rj ∈ C.gates := gate_mem C rj hrj
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ hm
      have huniq : ∀ q : Fin N, Relation.ReflTransGen (stp n C) (pw q) b → q = p := by
        intro q hq
        by_contra hne
        apply hb
        have hsub : ({q, p} : Set (Fin N)) ⊆
            {r : Fin N | Relation.ReflTransGen (stp n C) (pw r) b} := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hab
        calc 2 = ({q, p} : Set (Fin N)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun x hx => hx, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (stp n C) (pw p) ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hab
        · intro q hq
          apply huniq q
          rw [h0]; exact hq
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (stp n C) (pw p) ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hab
        · intro q hq
          apply huniq q
          rw [h1]; exact hq

theorem leafR (n : ℕ) (C : Circuit) (R : ℕ → ℕ → Prop) (t : ℕ) (L : List (ℕ × ℕ))
    (hT : ∀ Q : ℕ → List (ℕ × ℕ) → Prop,
      (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) →
      (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length →
        (gateAt C qj).op = GateOp.and → R (n + qj) qt →
        Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 →
        Q qt (qL1 ++ qL2)) → Q t L) :
    ∀ g ∈ L, R g.2 g.1 := by
  refine hT (fun t L => ∀ g ∈ L, R g.2 g.1) ?_ ?_
  · intro qv qt _ hR g hg
    rw [List.mem_singleton] at hg
    rw [hg]
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

theorem final {α : Type} [Finite α] (PA PX : α → Prop) (k : ℕ) (B : Set α) (hB : B.ncard ≤ k)
    (h : ∀ a, PA a → PX a → a ∈ B) :
    {a | PA a}.ncard ≤ k + {a | PA a ∧ ¬ PX a}.ncard := by
  have hsub : {a | PA a} ⊆ B ∪ {a | PA a ∧ ¬ PX a} := by
    intro a ha
    by_cases hx : PX a
    · exact Or.inl (h a ha hx)
    · exact Or.inr ⟨ha, hx⟩
  calc {a | PA a}.ncard ≤ (B ∪ {a | PA a ∧ ¬ PX a}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ B.ncard + {a | PA a ∧ ¬ PX a}.ncard := Set.ncard_union_le _ _
    _ ≤ k + {a | PA a ∧ ¬ PX a}.ncard := by omega

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  intro n N M pw lw I C hAO hpw hlw hne hpn hln hK hsound R hR T hT hread
  subst hT
  have hlen := hAO.2.2
  have hBex : ∀ ex : Fin N × Fin M, Bp N M pw I R ex → ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ {r : Fin N | R (pw r) (n + y.1)}.ncard ∧
      (∀ q : Fin N, R (pw q) (n + y.1) → I q ex.2) ∧
      R (pw ex.1) ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ q : Fin N, R (pw q) ((gateAt C y.1).inputs.getD y.2.val 0) → q = ex.1 := by
    rintro ex ⟨w, hw, hsh, h2⟩
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := key n N C pw hlen hpw hpn R hR ex.1 w hw h2
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun q hq => hsh q (h4 _ hq), h6, h7⟩
  choose! f hf using hBex
  have hO : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have hBcard : {ex : Fin N × Fin M | Bp N M pw I R ex}.ncard ≤
      2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
    have h1 : {ex : Fin N × Fin M | Bp N M pw I R ex}.ncard ≤
        ({jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} ×ˢ
          (Set.univ : Set (Fin 2))).ncard := by
      refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (hO.prod Set.finite_univ)
      · intro ex hex
        exact ⟨(hf ex hex).1, Set.mem_univ _⟩
      · intro ex hex ex2 hex2 heq
        have P1 := hf ex hex
        have P2 := hf ex2 hex2
        rw [← heq] at P2
        obtain ⟨_, h2a, hla, hra, hua⟩ := P1
        obtain ⟨_, _, hlb, hrb, hub⟩ := P2
        have e1 : ex2.1 = ex.1 := hua ex2.1 hrb
        obtain ⟨q1, q2, hq1, hq2, hq12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h2a
        have e2 : ex.2 = ex2.2 := by
          by_contra hl
          exact hK q1 q2 ex.2 ex2.2 hq12 hl ⟨hla q1 hq1, hla q2 hq2, hlb q1 hq1, hlb q2 hq2⟩
        exact Prod.ext e1.symm e2
    rw [Set.ncard_prod, Set.ncard_univ, Nat.card_fin] at h1
    omega
  refine final _ _ _ {ex : Fin N × Fin M | Bp N M pw I R ex} hBcard ?_
  intro a ha hx
  obtain ⟨L7, ⟨j7, La7, Lb7, hj7, hop7, hR7, hTa, hTb, hL⟩, hvars, hcp, hcl, g8, hg8, hg8p,
    hsh, h2⟩ := hx
  subst hL
  have hRg : R g8.2 g8.1 := by
    rcases List.mem_append.mp hg8 with h | h
    · exact leafR n C R _ La7 hTa g8 h
    · exact leafR n C R _ Lb7 hTb g8 h
  rw [hg8p] at hRg
  exact ⟨g8.1, hRg, hsh, h2⟩

end PEqualNP.Outside.L_meta_2409

theorem PEqualNP.Outside.L_meta_2409 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard :=
  PEqualNP.Outside.L_meta_2409.main_aux
