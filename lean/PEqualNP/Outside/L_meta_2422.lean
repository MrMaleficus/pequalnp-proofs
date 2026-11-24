import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2422

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

lemma and_pair (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (s t : ℕ)
    (hin : ((gateAt C j).inputs.getD 0 0 = s ∧ (gateAt C j).inputs.getD 1 0 = t) ∨
      ((gateAt C j).inputs.getD 0 0 = t ∧ (gateAt C j).inputs.getD 1 0 = s))
    (hs : W n C x s = true) (ht : W n C x t = true) : W n C x (n + j) = true := by
  rcases hin with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact and_up n C x hC j hj hop (by rw [e0]; exact hs) (by rw [e1]; exact ht)
  · exact and_up n C x hC j hj hop (by rw [e0]; exact ht) (by rw [e1]; exact hs)

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ (g c cb : ℕ), (g < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = c ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = cb) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = cb ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = c))) → R (n + g) C.output → ∀ (p : Fin N) (l' : Fin M) (h1 a v h2 u b : ℕ), (h1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = v) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = v ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {p} → (∃ m1 : Fin M, R (lw m1) v ∧ ¬ I p m1) → R (n + h1) c → (h2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = u ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = u))) → {y1 : Fin M | R (lw y1) b} = {l'} → (∃ z1 : Fin N, R (pw z1) u ∧ ¬ I z1 l') → R (n + h2) cb → ¬ I p l' → ∀ m : Fin M, R (lw m) v → ¬ I p m → ∀ z : Fin N, R (pw z) u → ¬ I z l' → I z m := by
  intro n N M pw lw I C hC hpw hlw hdisj hpn hln hsound R hR g c cb hg hgR p l' h1 a v h2 u b
    hsrc hsrcj hh1 hbot hbsh hbj hh2 hpl m hmv hpm z hzu hzl
  by_contra hzm
  obtain ⟨hg_lt, hg_op, hg_in⟩ := hg
  obtain ⟨⟨h1_lt, h1_op, h1_in⟩, hash⟩ := hsrc
  obtain ⟨h2_lt, h2_op, h2_in⟩ := hbot
  have hpa : R (pw p) a := by
    have hmem : p ∈ {x1 : Fin N | R (pw x1) a} := by
      rw [hash]
      exact Set.mem_singleton p
    exact hmem
  have hlb : R (lw l') b := by
    have hmem : l' ∈ {y1 : Fin M | R (lw y1) b} := by
      rw [hbsh]
      exact Set.mem_singleton l'
    exact hmem
  have hPcard : ({p, z} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
  have hYcard : ({m, l'} : Finset (Fin M)).card ≤ 2 := Finset.card_le_two
  have hno : ∀ p3 ∈ ({p, z} : Finset (Fin N)), ∀ l3 ∈ ({m, l'} : Finset (Fin M)), ¬ I p3 l3 := by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_insert, Finset.mem_singleton] at hp3 hl3
    rcases hp3 with hp3 | hp3 <;> rcases hl3 with hl3 | hl3 <;> rw [hp3, hl3] <;> assumption
  have big : ∀ x : Fin n → Bool, W n C x (pw p) = true → W n C x (lw m) = true →
      W n C x (pw z) = true → W n C x (lw l') = true → W n C x C.output = true := by
    intro x wp wm wz wl
    have wa := path_upR n C x R hR _ _ hpa wp
    have wv := path_upR n C x R hR _ _ hmv wm
    have wu := path_upR n C x R hR _ _ hzu wz
    have wb := path_upR n C x R hR _ _ hlb wl
    have wc := path_upR n C x R hR _ _ hh1 (and_pair n C x hC h1 h1_lt h1_op a v h1_in wa wv)
    have wcb := path_upR n C x R hR _ _ hh2 (and_pair n C x hC h2 h2_lt h2_op u b h2_in wu wb)
    exact path_upR n C x R hR _ _ hgR (and_pair n C x hC g hg_lt hg_op c cb hg_in wc wcb)
  refine finish n C _ (hsound {p, z} {m, l'} hPcard hYcard hno) (big _ ?_ ?_ ?_ ?_)
  · rw [W_input n C _ (pw p) (hpn p)]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw (Finset.mem_insert_self p _))
  · rw [W_input n C _ (lw m) (hln m)]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw (Finset.mem_insert_self m _))
  · rw [W_input n C _ (pw z) (hpn z)]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem pw
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self z)))
  · rw [W_input n C _ (lw l') (hln l')]
    simp only [decide_eq_true_eq]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem lw
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self l')))

end PEqualNP.Outside.L_meta_2422

theorem PEqualNP.Outside.L_meta_2422 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ (g c cb : ℕ), (g < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = c ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = cb) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 0 0) = cb ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD 1 0) = c))) → R (n + g) C.output → ∀ (p : Fin N) (l' : Fin M) (h1 a v h2 u b : ℕ), (h1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = v) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 0 0) = v ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h1).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {p} → (∃ m1 : Fin M, R (lw m1) v ∧ ¬ I p m1) → R (n + h1) c → (h2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C h2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = u ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C h2).inputs.getD 1 0) = u))) → {y1 : Fin M | R (lw y1) b} = {l'} → (∃ z1 : Fin N, R (pw z1) u ∧ ¬ I z1 l') → R (n + h2) cb → ¬ I p l' → ∀ m : Fin M, R (lw m) v → ¬ I p m → ∀ z : Fin N, R (pw z) u → ¬ I z l' → I z m :=
  PEqualNP.Outside.L_meta_2422.main_aux
