import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2355

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

lemma or_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : a < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ a ∈ (gateAt C rj).inputs)
    (ha : W n C z a = true) : W n C z b = true := by
  obtain ⟨hlt, rj, rfl, hj, hop, hin⟩ := h
  rw [W_gate n C z rj hj, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨a, hin, by simp only [hlt, ite_true]; exact ha⟩

lemma path_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (a b : ℕ)
    (h : Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs) a b)
    (ha : W n C z a = true) : W n C z b = true := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact or_up n C z _ _ hstep ih

lemma and_up (n : ℕ) (C : Circuit) (z : Fin n → Bool) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : W n C z ((gateAt C j).inputs.getD 0 0) = true)
    (h1 : W n C z ((gateAt C j).inputs.getD 1 0) = true) : W n C z (n + j) = true := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem C j hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [W_gate n C z j hj, hop]
  rw [hab] at h0 h1 hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  have h0' : W n C z a = true := by simpa using h0
  have h1' : W n C z b = true := by simpa using h1
  simp [GateOp.eval, ha, hb, h0', h1']

lemma path_upR (n : ℕ) (C : Circuit) (z : Fin n → Bool) (R : ℕ → ℕ → Prop)
    (hR : R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs)) (a b : ℕ)
    (h : R a b) (ha : W n C z a = true) : W n C z b = true := by
  subst hR
  exact path_up n C z a b h ha

lemma finish (n : ℕ) (C : Circuit) (z : Fin n → Bool) (hs : circuitFun n C z = false)
    (hW : W n C z C.output = true) : False := by
  have h : circuitFun n C z = W n C z C.output := rfl
  rw [h, hW] at hs
  cases hs

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l := by
  intro n N M pw lw I C hC hpw hlw hdisj hpn hln hsound R hR T hT p l L hI hyp
  obtain ⟨⟨j0, L1, L2, hj0, hop0, hR0, hT1, hT2, hLeq⟩, hvars, hcx, hcy⟩ := hyp
  subst hLeq
  have leafR : ∀ (top : ℕ) (L' : List (ℕ × ℕ)), T top L' → ∀ gv ∈ L', R gv.2 gv.1 := by
    intro top L' h
    subst hT
    refine h (fun _ L'' => ∀ gv ∈ L'', R gv.2 gv.1) ?_ ?_
    · intro qv qt _ hr gv hgv
      rw [List.mem_singleton] at hgv
      rw [hgv]
      exact hr
    · intro qj qt qL1 qL2 _ _ _ h1 h2 gv hgv
      rcases List.mem_append.mp hgv with h' | h'
      · exact h1 gv h'
      · exact h2 gv h'
  have tree : ∀ (z : Fin n → Bool) (top : ℕ) (L' : List (ℕ × ℕ)), T top L' →
      (∀ gv ∈ L', W n C z gv.1 = true) → W n C z top = true := by
    intro z top L' h
    subst hT
    refine h (fun t L'' => (∀ gv ∈ L'', W n C z gv.1 = true) → W n C z t = true) ?_ ?_
    · intro qv qt _ _ hm
      exact hm (qt, qv) (List.mem_singleton.mpr rfl)
    · intro qj qt qL1 qL2 hj hop hr hq1 hq2 hm
      refine path_upR n C z R hR (n + qj) qt hr ?_
      refine and_up n C z hC qj hj hop (hq1 ?_) (hq2 ?_)
      · intro gv hmem
        exact hm gv (List.mem_append_left _ hmem)
      · intro gv hmem
        exact hm gv (List.mem_append_right _ hmem)
  by_contra hcon
  have hcon' : ∀ gv ∈ L1 ++ L2, gv.2 = pw p → ∃ q : Fin N, R (pw q) gv.1 ∧ ¬ I q l := by
    intro gv hgv hx
    by_contra hno
    apply hcon
    refine ⟨gv, hgv, hx, ?_⟩
    intro q hq
    by_contra hI'
    exact hno ⟨q, hq, hI'⟩
  have hex : ∀ gv : ℕ × ℕ, ∃ q : Fin N,
      (gv ∈ L1 ++ L2 → gv.2 = pw p → R (pw q) gv.1 ∧ ¬ I q l) := by
    intro gv
    by_cases h : gv ∈ L1 ++ L2 ∧ gv.2 = pw p
    · obtain ⟨q, hq⟩ := hcon' gv h.1 h.2
      exact ⟨q, fun _ _ => hq⟩
    · exact ⟨p, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose f hf using hex
  obtain ⟨Lx, hLx⟩ : ∃ Lx : List (ℕ × ℕ),
      Lx = (L1 ++ L2).filter (fun e1 => decide (e1.2 = pw p)) := ⟨_, rfl⟩
  have hx2 : Lx.length ≤ 2 := by
    rw [hLx]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcx
    omega
  obtain ⟨P, hP⟩ : ∃ P : Finset (Fin N), P = (Lx.map f).toFinset := ⟨_, rfl⟩
  have hPcard : P.card ≤ 2 := by
    rw [hP]
    refine le_trans (List.toFinset_card_le _) ?_
    rw [List.length_map]
    exact hx2
  have hYcard : ({l} : Finset (Fin M)).card ≤ 2 := by
    rw [Finset.card_singleton]
    omega
  have hno : ∀ p3 ∈ P, ∀ l3 ∈ ({l} : Finset (Fin M)), ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hl3
    rw [hl3]
    rw [hP, List.mem_toFinset, List.mem_map] at hp3
    obtain ⟨gv, hgv, hfg⟩ := hp3
    rw [hLx] at hgv
    have hm := List.mem_filter.mp hgv
    rw [← hfg]
    exact (hf gv hm.1 (of_decide_eq_true hm.2)).2
  have big : ∀ z : Fin n → Bool, (∀ q ∈ P, W n C z (pw q) = true) →
      W n C z (lw l) = true → W n C z C.output = true := by
    intro z hzP hzl
    have hleaf : ∀ gv ∈ L1 ++ L2, W n C z gv.1 = true := by
      intro gv hgv
      have hr : R gv.2 gv.1 := by
        rcases List.mem_append.mp hgv with h' | h'
        · exact leafR _ L1 hT1 gv h'
        · exact leafR _ L2 hT2 gv h'
      rcases hvars gv hgv with hx | hy
      · have hfg := hf gv hgv hx
        refine path_upR n C z R hR (pw (f gv)) gv.1 hfg.1 (hzP _ ?_)
        rw [hP, List.mem_toFinset, List.mem_map]
        refine ⟨gv, ?_, rfl⟩
        rw [hLx]
        exact List.mem_filter.mpr ⟨hgv, decide_eq_true hx⟩
      · rw [hy] at hr
        exact path_upR n C z R hR (lw l) gv.1 hr hzl
    have h0 := tree z _ L1 hT1 (fun gv h' => hleaf gv (List.mem_append_left _ h'))
    have h1 := tree z _ L2 hT2 (fun gv h' => hleaf gv (List.mem_append_right _ h'))
    exact path_upR n C z R hR (n + j0) C.output hR0 (and_up n C z hC j0 hj0 hop0 h0 h1)
  refine finish n C _ (hsound P {l} hPcard hYcard hno) (big _ ?_ ?_)
  · intro q hq
    rw [W_input n C _ (pw q) (hpn q)]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw hq)
  · rw [W_input n C _ (lw l) (hln l)]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_singleton_self l))

end PEqualNP.Outside.L_meta_2355

theorem PEqualNP.Outside.L_meta_2355 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (p : Fin N) (l : Fin M) (L : List (ℕ × ℕ)), I p l → ((∃ (j0 : ℕ) (L1 L2 : List (ℕ × ℕ)), j0 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j0).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j0) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 0 0) L1 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j0).inputs.getD 1 0) L2 ∧ L = L1 ++ L2) ∧ (∀ gv ∈ L, gv.2 = pw p ∨ gv.2 = lw l) ∧ (L.filter (fun e1 => decide (e1.2 = pw p))).length ∈ ({1, 2} : Finset ℕ) ∧ (L.filter (fun e2 => decide (e2.2 = lw l))).length ∈ ({1, 2} : Finset ℕ)) → ∃ gv ∈ L, gv.2 = pw p ∧ ∀ q : Fin N, R (pw q) gv.1 → I q l :=
  PEqualNP.Outside.L_meta_2355.main_aux
