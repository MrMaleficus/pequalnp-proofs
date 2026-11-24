import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2414

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

private def mstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (mstep w g).length = w.length + 1 := by
  simp [mstep]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (mstep w g).getD i false = w.getD i false := by
  simp [mstep, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (mstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [mstep, List.getD]

private def MW {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl mstep (List.ofFn x)

private lemma MW_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (MW gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl mstep w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [MW, h]
  simp

private lemma MW_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    MW (gs ++ [g]) x = mstep (MW gs x) g := by
  simp [MW, List.foldl_append]

private lemma MW_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (MW (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (MW gs x).getD i false)
      else (MW gs x).getD t false := by
  rw [MW_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [MW_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [MW_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, MW_len]; omega),
        List.getD_eq_default _ _ (by rw [MW_len]; omega)]

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (MW gs x).getD t false = true → (MW gs y).getD t false = true

private lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

private lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [MW_val] at ht ⊢
  by_cases htt : t = n + gs.length
  · rw [if_pos htt] at ht ⊢
    rcases hop with hand | hor
    · rw [hand] at ht ⊢
      exact (all_true _ _).mpr (fun i hi => h x y hxy i ((all_true _ _).mp ht i hi))
    · rw [hor] at ht ⊢
      obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
      exact (any_true _ _).mpr ⟨i, hi, h x y hxy i hti⟩
  · rw [if_neg htt] at ht ⊢
    exact h x y hxy t ht

private lemma mono_all {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact mono_nil
  | append_singleton gs g ih =>
    exact mono_step gs g (hg g (by simp)) (ih (fun g' hg' => hg g' (by simp [hg'])))

private lemma wires_mono (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (t : ℕ)
    (h : (C.wires (List.ofFn x)).getD t false = true) :
    (C.wires (List.ofFn y)).getD t false = true :=
  mono_all C.gates hC x y hxy t h

lemma mem_of_getD (L : List ℕ) (hL : L.length = 2) :
    L.getD 0 0 ∈ L ∧ L.getD 1 0 ∈ L ∧ ∀ u ∈ L, u = L.getD 0 0 ∨ u = L.getD 1 0 := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hL
  simp

lemma tag_facts (p : Prop) [Decidable p] :
    (if p then 2 else 3 : ℕ) < 4 ∧ 2 ≤ (if p then 2 else 3 : ℕ) ∧
      ((if p then 2 else 3 : ℕ) = 2 ↔ p) := by
  by_cases h : p <;> simp [h]

lemma exists_min (P : ℕ → Prop) (h : ∃ v, P v) : ∃ w, P w ∧ ∀ v, v < w → ¬ P v := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun v hv => Nat.find_min h hv⟩

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m Mg d m2 S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ ((Mg e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (d e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (m2 e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (m2 e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (d e)))) ∧ R (n + Mg e) (m e) ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m2 e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ z4 : Fin n → Bool, (∃ h4 : pw e.1 < n, z4 ⟨pw e.1, h4⟩ = true) → (C.wires (List.ofFn z4)).getD ((m2 e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z4 = true) ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7.val = pw e.1)))).getD ((d e)) false = true ∧ (∀ pz5 : Fin N, ¬ I pz5 e.2 → ∃ (P5 : Finset (Fin N)) (Y5 : Finset (Fin M)), P5.card ≤ 1 ∧ Y5.card ≤ 2 ∧ (∀ a5 ∈ insert pz5 P5, ∀ m5 ∈ Y5, ¬ I a5 m5) ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val ∈ P5.image pw ∪ Y5.image lw)))).getD ((n + Mg e)) false = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 4 * C.size := by
  intro n N M pw lw I C A Rd G m Mg d m2 S Sy hC hpw hlw hpl hpn hln hK hsound R hR hA
  obtain ⟨hAO, hRB, hLen⟩ := hC
  have hLen2 : ∀ j, j < C.gates.length → (gateAt C j).inputs.length = 2 :=
    fun j hj => hLen _ (gateAt_mem C j hj)
  -- abstract facts about the OR-reach relation
  have hRrefl : ∀ a, R a a := by
    intro a; subst hR; exact Relation.ReflTransGen.refl
  have hRtrans : ∀ a b c, R a b → R b c → R a c := by
    intro a b c h1 h2; subst hR; exact h1.trans h2
  have hRstep : ∀ u b, (u < b ∧ ∃ rj, b = n + rj ∧ rj < C.gates.length ∧
      (gateAt C rj).op = GateOp.or ∧ u ∈ (gateAt C rj).inputs) → R u b := by
    intro u b h; subst hR; exact Relation.ReflTransGen.single h
  have hRcases : ∀ a b, R a b → a = b ∨ ∃ u, R a u ∧ u < b ∧ ∃ rj, b = n + rj ∧
      rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧ u ∈ (gateAt C rj).inputs := by
    intro a b h; subst hR
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨u, hu, hlt, hex⟩
    · exact Or.inl heq.symm
    · exact Or.inr ⟨u, hu, hlt, hex⟩
  have hRup : ∀ (z : Fin n → Bool) (a b : ℕ), R a b → W n C z a = true → W n C z b = true :=
    fun z a b h ha => path_upR n C z R hR a b h ha
  -- acceptance
  have hAcc : ∀ e ∈ A, ∀ μ, (μ = m e ∨ μ = m2 e) → ∀ z : Fin n → Bool,
      z ⟨pw e.1, hpn e.1⟩ = true → W n C z μ = true → circuitFun n C z = true := by
    intro e he μ hμ z hz hw
    obtain ⟨-, -, -, -, -, -, -, -, hacc1, hacc2, -, -, -⟩ := hA e he
    rcases hμ with rfl | rfl
    · exact hacc1 z ⟨hpn e.1, hz⟩ hw
    · exact hacc2 z ⟨hpn e.1, hz⟩ hw
  -- a dirty gate OR-below an accepting wire forces an incidence
  have hKey : ∀ e ∈ A, ∀ e' ∈ A, ∀ g, (g = Mg e' ∨ g = S e') → ∀ μ, (μ = m e ∨ μ = m2 e) →
      R (n + g) μ → I e.1 e'.2 := by
    intro e he e' he' g hg μ hμ hreach
    by_contra hnI
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hdirtM, hdirtS⟩ := hA e' he'
    have hdirt : ∃ (P5 : Finset (Fin N)) (Y5 : Finset (Fin M)), P5.card ≤ 1 ∧ Y5.card ≤ 2 ∧
        (∀ a5 ∈ insert e.1 P5, ∀ m5 ∈ Y5, ¬ I a5 m5) ∧
        W n C (fun k5 : Fin n => decide (k5.val ∈ P5.image pw ∪ Y5.image lw)) (n + g) = true := by
      rcases hg with rfl | rfl
      · exact hdirtM e.1 hnI
      · exact hdirtS e.1 hnI
    obtain ⟨P5, Y5, hP5, hY5, hno, hw⟩ := hdirt
    have hw' : W n C (fun k : Fin n => decide (k.val ∈ (insert e.1 P5).image pw ∪ Y5.image lw))
        (n + g) = true := by
      refine wires_mono n C hAO _ _ ?_ (n + g) hw
      intro i hi
      simp only [decide_eq_true_eq, Finset.mem_union, Finset.mem_image, Finset.mem_insert] at hi ⊢
      rcases hi with ⟨a, ha, hax⟩ | h
      · exact Or.inl ⟨a, Or.inr ha, hax⟩
      · exact Or.inr h
    have h1 : circuitFun n C
        (fun k : Fin n => decide (k.val ∈ (insert e.1 P5).image pw ∪ Y5.image lw)) = true := by
      refine hAcc e he μ hμ _ ?_ (hRup _ _ _ hreach hw')
      exact decide_eq_true (Finset.mem_union_left _
        (Finset.mem_image_of_mem pw (Finset.mem_insert_self _ _)))
    have h2 := hsound (insert e.1 P5) Y5 ((Finset.card_insert_le _ _).trans (by omega)) hY5 hno
    exact Bool.noConfusion (h1.symm.trans h2)
  -- an accepting wire is false on two points
  have hTwo : ∀ e ∈ A, ∀ μ, (μ = m e ∨ μ = m2 e) → ∀ q : Fin N,
      W n C (fun k : Fin n => decide (k.val ∈ ({q, e.1} : Finset (Fin N)).image pw ∪
        (∅ : Finset (Fin M)).image lw)) μ = true → False := by
    intro e he μ hμ q hw
    have h1 : circuitFun n C (fun k : Fin n => decide (k.val ∈
        ({q, e.1} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw)) = true := by
      refine hAcc e he μ hμ _ ?_ hw
      exact decide_eq_true (Finset.mem_union_left _
        (Finset.mem_image_of_mem pw (by simp)))
    have h2 := hsound {q, e.1} ∅ Finset.card_le_two (by simp)
      (by intro p3 _ l3 hl3; simp at hl3)
    exact Bool.noConfusion (h1.symm.trans h2)
  have hNoPt : ∀ e ∈ A, ∀ μ, (μ = m e ∨ μ = m2 e) → ∀ q : Fin N, ¬ R (pw q) μ := by
    intro e he μ hμ q hreach
    refine hTwo e he μ hμ q (hRup _ _ _ hreach ?_)
    rw [W_input n C _ (pw q) (hpn q)]
    exact decide_eq_true (Finset.mem_union_left _
      (Finset.mem_image_of_mem pw (by simp)))
  have hDneq : ∀ e ∈ A, ∀ e' ∈ A, d e ≠ m2 e' := by
    intro e he e' he' heq
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hd, -, -⟩ := hA e he
    refine hTwo e' he' (m2 e') (Or.inr rfl) e.1 ?_
    rw [← heq]
    refine wires_mono n C hAO _ _ ?_ (d e) hd
    intro i hi
    simp only [decide_eq_true_eq, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
      Finset.mem_singleton] at hi ⊢
    exact Or.inl ⟨e.1, Or.inl rfl, hi.symm⟩
  have hGmem : ∀ e ∈ A, R (pw e.1) (G e) := by
    intro e he
    obtain ⟨-, -, hGsh, -⟩ := hA e he
    exact (Set.ext_iff.mp hGsh e.1).mpr (Set.mem_singleton _)
  have hRdUniq : ∀ e ∈ A, ∀ e' ∈ A, Rd e = Rd e' → G e = G e' ∧ m e = m e' := by
    intro e he e' he' heq
    obtain ⟨-, ⟨-, -, hin⟩, -⟩ := hA e he
    obtain ⟨-, ⟨-, -, hin'⟩, -⟩ := hA e' he'
    rw [← heq] at hin'
    rcases hin with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hin' with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
    · exact ⟨h0.symm.trans h0', h1.symm.trans h1'⟩
    · have hGm : G e = m e' := h0.symm.trans h0'
      have h := hGmem e he
      rw [hGm] at h
      exact absurd h (hNoPt e' he' (m e') (Or.inl rfl) e.1)
    · have hGm : G e' = m e := h0'.symm.trans h0
      have h := hGmem e' he'
      rw [hGm] at h
      exact absurd h (hNoPt e he (m e) (Or.inl rfl) e'.1)
    · exact ⟨h1.symm.trans h1', h0.symm.trans h0'⟩
  have hMgUniq : ∀ e ∈ A, ∀ e' ∈ A, Mg e = Mg e' → m2 e = m2 e' := by
    intro e he e' he' heq
    obtain ⟨-, -, -, ⟨-, -, hin⟩, -⟩ := hA e he
    obtain ⟨-, -, -, ⟨-, -, hin'⟩, -⟩ := hA e' he'
    rw [← heq] at hin'
    rcases hin with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hin' with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
    · exact h1.symm.trans h1'
    · exact absurd (h0.symm.trans h0') (hDneq e he e' he')
    · exact absurd (h0'.symm.trans h0) (hDneq e' he' e he)
    · exact h0.symm.trans h0'
  -- the lines seen below a wire
  obtain ⟨InL, hInL⟩ : ∃ InL : ℕ → Fin M → Prop, ∀ w l, InL w l ↔
      ∃ e' ∈ A, e'.2 = l ∧ (R (n + S e') w ∨ R (n + Mg e') w) :=
    ⟨fun w l => ∃ e' ∈ A, e'.2 = l ∧ (R (n + S e') w ∨ R (n + Mg e') w), fun _ _ => Iff.rfl⟩
  have hKey2 : ∀ e ∈ A, ∀ w, (R w (m e) ∨ R w (m2 e)) → ∀ l, InL w l → I e.1 l := by
    intro e he w hw l hl
    obtain ⟨e', he', rfl, hr⟩ := (hInL w l).mp hl
    rcases hr with hr | hr <;> rcases hw with hw | hw
    · exact hKey e he e' he' (S e') (Or.inr rfl) (m e) (Or.inl rfl) (hRtrans _ _ _ hr hw)
    · exact hKey e he e' he' (S e') (Or.inr rfl) (m2 e) (Or.inr rfl) (hRtrans _ _ _ hr hw)
    · exact hKey e he e' he' (Mg e') (Or.inl rfl) (m e) (Or.inl rfl) (hRtrans _ _ _ hr hw)
    · exact hKey e he e' he' (Mg e') (Or.inl rfl) (m2 e) (Or.inr rfl) (hRtrans _ _ _ hr hw)
  have hUniqP : ∀ e ∈ A, ∀ e' ∈ A, ∀ w, (R w (m e) ∨ R w (m2 e)) → (R w (m e') ∨ R w (m2 e')) →
      ∀ l1 l2, InL w l1 → InL w l2 → l1 ≠ l2 → e.1 = e'.1 := by
    intro e he e' he' w hw hw' l1 l2 hl1 hl2 hne
    by_contra hp
    exact hK e.1 e'.1 l1 l2 hp hne ⟨hKey2 e he w hw l1 hl1, hKey2 e' he' w hw' l1 hl1,
      hKey2 e he w hw l2 hl2, hKey2 e' he' w hw' l2 hl2⟩
  -- the charge of an incidence
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin N × Fin M → ℕ × ℕ → Prop, ∀ e c, Φ e c ↔
      ((c.1 = 0 ∧ c.2 = Rd e ∧ ∀ l, InL (m e) l → l = e.2) ∨
       (c.1 = 1 ∧ c.2 = Mg e ∧ (∀ l, InL (m2 e) l → l = e.2) ∧
          ∃ l1 l2, InL (n + Mg e) l1 ∧ InL (n + Mg e) l2 ∧ l1 ≠ l2) ∨
       (2 ≤ c.1 ∧ c.2 = S e ∧ (c.1 = 2 ↔ (gateAt C (S e)).inputs.getD 0 0 = Sy e) ∧
          ∃ l1 l2, InL (n + S e) l1 ∧ InL (n + S e) l2 ∧ l1 ≠ l2) ∨
       (2 ≤ c.1 ∧ (gateAt C c.2).op = GateOp.or ∧ (R (n + c.2) (m e) ∨ R (n + c.2) (m2 e)) ∧
          (∃ u, (c.1 = 2 ↔ (gateAt C c.2).inputs.getD 0 0 = u) ∧ u ∈ (gateAt C c.2).inputs ∧
            (∀ l, InL u l → l = e.2) ∧ InL u e.2) ∧
          ∃ l1 l2, InL (n + c.2) l1 ∧ InL (n + c.2) l2 ∧ l1 ≠ l2)) :=
    ⟨_, fun _ _ => Iff.rfl⟩
  have hCharge : ∀ e ∈ A, ∃ c : ℕ × ℕ, c.1 < 4 ∧ c.2 < C.gates.length ∧ Φ e c := by
    intro e he
    obtain ⟨-, ⟨hRdlt, -, -⟩, -, ⟨hMglt, -, hMgin⟩, hMgm, ⟨o, hSlt, -, -⟩, -, hSm2, -⟩ := hA e he
    by_cases hbad : ∃ v, ((R (n + S e) v ∧ R v (m2 e)) ∨ (R (n + Mg e) v ∧ R v (m e))) ∧
        ∃ l, InL v l ∧ l ≠ e.2
    · obtain ⟨w, ⟨hchain, l2, hl2, hne2⟩, hmin⟩ := exists_min _ hbad
      have hInLw : InL w e.2 := by
        rcases hchain with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact (hInL _ _).mpr ⟨e, he, rfl, Or.inl h1⟩
        · exact (hInL _ _).mpr ⟨e, he, rfl, Or.inr h1⟩
      have hsplit : ∃ l1 l2, InL w l1 ∧ InL w l2 ∧ l1 ≠ l2 := ⟨l2, e.2, hl2, hInLw, hne2⟩
      rcases hchain with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hRcases _ _ h1 with heq | ⟨u, hu1, hult, rj, hwj, hjlt, hjop, huin⟩
        · subst heq
          exact ⟨(if (gateAt C (S e)).inputs.getD 0 0 = Sy e then 2 else 3, S e),
            (tag_facts _).1, hSlt, (hΦ _ _).mpr (Or.inr (Or.inr (Or.inl
              ⟨(tag_facts _).2.1, rfl, (tag_facts _).2.2, hsplit⟩)))⟩
        · subst hwj
          have hRuw : R u (n + rj) := hRstep _ _ ⟨hult, rj, rfl, hjlt, hjop, huin⟩
          refine ⟨(if (gateAt C rj).inputs.getD 0 0 = u then 2 else 3, rj),
            (tag_facts _).1, hjlt, (hΦ _ _).mpr (Or.inr (Or.inr (Or.inr
              ⟨(tag_facts _).2.1, hjop, Or.inr h2, ⟨u, (tag_facts _).2.2, huin, ?_, ?_⟩,
                hsplit⟩)))⟩
          · intro l hl
            by_contra hne
            exact hmin u hult ⟨Or.inl ⟨hu1, hRtrans _ _ _ hRuw h2⟩, l, hl, hne⟩
          · exact (hInL _ _).mpr ⟨e, he, rfl, Or.inl hu1⟩
      · rcases hRcases _ _ h1 with heq | ⟨u, hu1, hult, rj, hwj, hjlt, hjop, huin⟩
        · subst heq
          have hm2lt : m2 e < n + Mg e := by
            obtain ⟨hm0, hm1, -⟩ := mem_of_getD _ (hLen2 (Mg e) hMglt)
            rcases hMgin with ⟨-, hb⟩ | ⟨ha, -⟩
            · rw [hb] at hm1
              exact hRB (Mg e) hMglt _ hm1
            · rw [ha] at hm0
              exact hRB (Mg e) hMglt _ hm0
          refine ⟨(1, Mg e), by norm_num, hMglt,
            (hΦ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl, ?_, hsplit⟩))⟩
          intro l hl
          by_contra hne
          exact hmin (m2 e) hm2lt ⟨Or.inl ⟨hSm2, hRrefl _⟩, l, hl, hne⟩
        · subst hwj
          have hRuw : R u (n + rj) := hRstep _ _ ⟨hult, rj, rfl, hjlt, hjop, huin⟩
          refine ⟨(if (gateAt C rj).inputs.getD 0 0 = u then 2 else 3, rj),
            (tag_facts _).1, hjlt, (hΦ _ _).mpr (Or.inr (Or.inr (Or.inr
              ⟨(tag_facts _).2.1, hjop, Or.inl h2, ⟨u, (tag_facts _).2.2, huin, ?_, ?_⟩,
                hsplit⟩)))⟩
          · intro l hl
            by_contra hne
            exact hmin u hult ⟨Or.inr ⟨hu1, hRtrans _ _ _ hRuw h2⟩, l, hl, hne⟩
          · exact (hInL _ _).mpr ⟨e, he, rfl, Or.inr hu1⟩
    · refine ⟨(0, Rd e), by norm_num, hRdlt, (hΦ _ _).mpr (Or.inl ⟨rfl, rfl, ?_⟩)⟩
      intro l hl
      by_contra hne
      exact hbad ⟨m e, Or.inr ⟨hMgm, hRrefl _⟩, l, hl, hne⟩
  -- a charge determines its incidence
  have hInj : ∀ e ∈ A, ∀ e' ∈ A, ∀ c : ℕ × ℕ, c.2 < C.gates.length → Φ e c → Φ e' c →
      e = e' := by
    intro e he e' he' c hc h h'
    obtain ⟨-, -, hGsh, -, hMgm, ⟨o, -, hSop, hSin⟩, hSysh, hSm2, -⟩ := hA e he
    obtain ⟨-, -, hGsh', -, hMgm', ⟨o', -, hSop', hSin'⟩, hSysh', hSm2', -⟩ := hA e' he'
    rcases (hΦ _ _).mp h with ⟨ht, hj, hL⟩ | ⟨ht, hj, hL, l1, l2, hl1, hl2, hne⟩ |
      ⟨ht, hj, hpos, l1, l2, hl1, hl2, hne⟩ |
      ⟨ht, hjop, hreach, ⟨u, hpos, huin, huL, huself⟩, l1, l2, hl1, hl2, hne⟩
    · rcases (hΦ _ _).mp h' with ⟨ht', hj', hL'⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩
      · have hRdeq : Rd e = Rd e' := hj.symm.trans hj'
        obtain ⟨hGeq, hmeq⟩ := hRdUniq e he e' he' hRdeq
        have hp : e'.1 = e.1 := by
          have h1 : e'.1 ∈ {x1 : Fin N | R (pw x1) (G e)} := by
            show R (pw e'.1) (G e)
            rw [hGeq]
            exact hGmem e' he'
          exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hGsh e'.1).mp h1)
        have hl : e'.2 = e.2 := by
          refine hL e'.2 ((hInL _ _).mpr ⟨e', he', rfl, Or.inr ?_⟩)
          rw [hmeq]
          exact hMgm'
        exact (Prod.ext hp hl).symm
      · omega
      · omega
      · omega
    · rcases (hΦ _ _).mp h' with ⟨ht', -⟩ | ⟨ht', hj', hL', -⟩ | ⟨ht', -⟩ | ⟨ht', -⟩
      · omega
      · have hMgeq : Mg e = Mg e' := hj.symm.trans hj'
        have hm2eq := hMgUniq e he e' he' hMgeq
        have hl : e'.2 = e.2 := by
          refine hL e'.2 ((hInL _ _).mpr ⟨e', he', rfl, Or.inl ?_⟩)
          rw [hm2eq]
          exact hSm2'
        have hp : e.1 = e'.1 := by
          refine hUniqP e he e' he' (n + Mg e) (Or.inl hMgm) (Or.inl ?_) l1 l2 hl1 hl2 hne
          rw [hMgeq]
          exact hMgm'
        exact Prod.ext hp hl.symm
      · omega
      · omega
    · rcases (hΦ _ _).mp h' with ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', hj', hpos', -⟩ | ⟨ht', hjop', -⟩
      · omega
      · omega
      · have hSeq : S e = S e' := hj.symm.trans hj'
        rw [← hSeq] at hpos' hSin'
        have hSy : Sy e = Sy e' := by
          by_cases h2 : c.1 = 2
          · exact (hpos.mp h2).symm.trans (hpos'.mp h2)
          · have hn : ¬ (gateAt C (S e)).inputs.getD 0 0 = Sy e := fun hh => h2 (hpos.mpr hh)
            have hn' : ¬ (gateAt C (S e)).inputs.getD 0 0 = Sy e' :=
              fun hh => h2 (hpos'.mpr hh)
            rcases hSin with ⟨ha, -⟩ | ⟨-, hb⟩
            · exact absurd ha hn
            · rcases hSin' with ⟨ha', -⟩ | ⟨-, hb'⟩
              · exact absurd ha' hn'
              · exact hb.symm.trans hb'
        have hl : e'.2 = e.2 := by
          have h1 : e'.2 ∈ {y2 : Fin M | R (lw y2) (Sy e)} := by
            show R (lw e'.2) (Sy e)
            rw [hSy]
            exact (Set.ext_iff.mp hSysh' e'.2).mpr (Set.mem_singleton _)
          exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp hSysh e'.2).mp h1)
        have hp : e.1 = e'.1 := by
          refine hUniqP e he e' he' (n + S e) (Or.inr hSm2) (Or.inr ?_) l1 l2 hl1 hl2 hne
          rw [hSeq]
          exact hSm2'
        exact Prod.ext hp hl.symm
      · rw [hj, hSop] at hjop'
        exact GateOp.noConfusion hjop'
    · rcases (hΦ _ _).mp h' with ⟨ht', -⟩ | ⟨ht', -⟩ | ⟨ht', hj', -⟩ |
        ⟨ht', hjop', hreach', ⟨u', hpos', huin', huL', huself'⟩, -⟩
      · omega
      · omega
      · rw [hj', hSop'] at hjop
        exact GateOp.noConfusion hjop
      · obtain ⟨-, -, htwo⟩ := mem_of_getD _ (hLen2 c.2 hc)
        have huu : u = u' := by
          by_cases h2 : c.1 = 2
          · exact (hpos.mp h2).symm.trans (hpos'.mp h2)
          · have hn : ¬ u = (gateAt C c.2).inputs.getD 0 0 := fun hh => h2 (hpos.mpr hh.symm)
            have hn' : ¬ u' = (gateAt C c.2).inputs.getD 0 0 :=
              fun hh => h2 (hpos'.mpr hh.symm)
            rcases htwo u huin with hh | hh
            · exact absurd hh hn
            · rcases htwo u' huin' with hh' | hh'
              · exact absurd hh' hn'
              · exact hh.trans hh'.symm
        have hl : e.2 = e'.2 := by
          refine huL' e.2 ?_
          rw [← huu]
          exact huself
        have hp : e.1 = e'.1 := hUniqP e he e' he' (n + c.2) hreach hreach' l1 l2 hl1 hl2 hne
        exact Prod.ext hp hl
  -- counting
  have hCh : ∀ e : Fin N × Fin M, ∃ c : ℕ × ℕ, e ∈ A →
      (c.1 < 4 ∧ c.2 < C.gates.length ∧ Φ e c) := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨c, hc⟩ := hCharge e he
      exact ⟨c, fun _ => hc⟩
    · exact ⟨(0, 0), fun h => absurd h he⟩
  choose f hf using hCh
  have hinj : Set.InjOn f (A : Set (Fin N × Fin M)) := by
    intro e he e' he' hff
    have he1 : e ∈ A := Finset.mem_coe.mp he
    have he2 : e' ∈ A := Finset.mem_coe.mp he'
    refine hInj e he1 e' he2 (f e) (hf e he1).2.1 (hf e he1).2.2 ?_
    rw [hff]
    exact (hf e' he2).2.2
  have hsub : A.image f ⊆ Finset.range 4 ×ˢ Finset.range C.gates.length := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hf e he).1, Finset.mem_range.mpr (hf e he).2.1⟩
  have hfin := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
    Finset.card_range] at hfin
  exact hfin

end PEqualNP.Outside.L_meta_2414

theorem PEqualNP.Outside.L_meta_2414 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)) (Rd G m Mg d m2 S Sy : Fin N × Fin M → ℕ), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, I e.1 e.2 ∧ ((Rd e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (G e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (m e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 0 0) = (m e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Rd e)).inputs.getD 1 0) = (G e)))) ∧ {x1 : Fin N | R (pw x1) (G e)} = {e.1} ∧ ((Mg e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (d e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (m2 e)) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 0 0) = (m2 e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (Mg e)).inputs.getD 1 0) = (d e)))) ∧ R (n + Mg e) (m e) ∧ (∃ o : ℕ, ((S e) < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = (Sy e) ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = o) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 0 0) = o ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (S e)).inputs.getD 1 0) = (Sy e))))) ∧ {y2 : Fin M | R (lw y2) (Sy e)} = {e.2} ∧ R (n + S e) (m2 e) ∧ (∀ z3 : Fin n → Bool, (∃ h3 : pw e.1 < n, z3 ⟨pw e.1, h3⟩ = true) → (C.wires (List.ofFn z3)).getD ((m e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z3 = true) ∧ (∀ z4 : Fin n → Bool, (∃ h4 : pw e.1 < n, z4 ⟨pw e.1, h4⟩ = true) → (C.wires (List.ofFn z4)).getD ((m2 e)) false = true → PEqualNP.MetaComplexity.circuitFun n C z4 = true) ∧ (C.wires (List.ofFn (fun k7 : Fin n => decide (k7.val = pw e.1)))).getD ((d e)) false = true ∧ (∀ pz5 : Fin N, ¬ I pz5 e.2 → ∃ (P5 : Finset (Fin N)) (Y5 : Finset (Fin M)), P5.card ≤ 1 ∧ Y5.card ≤ 2 ∧ (∀ a5 ∈ insert pz5 P5, ∀ m5 ∈ Y5, ¬ I a5 m5) ∧ (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val ∈ P5.image pw ∪ Y5.image lw)))).getD ((n + Mg e)) false = true) ∧ (∀ pz6 : Fin N, ¬ I pz6 e.2 → ∃ (P6 : Finset (Fin N)) (Y6 : Finset (Fin M)), P6.card ≤ 1 ∧ Y6.card ≤ 2 ∧ (∀ a6 ∈ insert pz6 P6, ∀ m6 ∈ Y6, ¬ I a6 m6) ∧ (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val ∈ P6.image pw ∪ Y6.image lw)))).getD ((n + S e)) false = true)) → A.card ≤ 4 * C.size :=
  PEqualNP.Outside.L_meta_2414.main_aux
