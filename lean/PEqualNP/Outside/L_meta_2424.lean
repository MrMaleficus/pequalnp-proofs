import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2424

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- fragment f00_basic
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

-- fragment f01_tools
def stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

def Rr (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (stp n C)

def inp (C : Circuit) (j : ℕ) (b : Bool) : ℕ := (gateAt C j).inputs.getD (if b then 1 else 0) 0

def AndG (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.and

def OrG (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.or

theorem inp_false (C : Circuit) (j : ℕ) : inp C j false = (gateAt C j).inputs.getD 0 0 := by
  simp [inp]

theorem inp_true (C : Circuit) (j : ℕ) : inp C j true = (gateAt C j).inputs.getD 1 0 := by
  simp [inp]

theorem Rr_refl (n : ℕ) (C : Circuit) (a : ℕ) : Rr n C a a := Relation.ReflTransGen.refl

theorem Rr_trans {n : ℕ} {C : Circuit} {a b c : ℕ} (h1 : Rr n C a b) (h2 : Rr n C b c) : Rr n C a c :=
  Relation.ReflTransGen.trans h1 h2

theorem inp_cases {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (u : ℕ) (hu : u ∈ (gateAt C j).inputs) : ∃ b, u = inp C j b := by
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ (gateAt_mem C j hj)
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  rw [hxy] at hu
  rcases List.mem_pair.mp hu with h | h
  · exact ⟨false, by rw [inp_false, hxy, h]; rfl⟩
  · exact ⟨true, by rw [inp_true, hxy, h]; rfl⟩

theorem inp_mem {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (b : Bool) :
    inp C j b ∈ (gateAt C j).inputs ∧ inp C j b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := hC.2.2 _ (gateAt_mem C j hj)
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  have hm : inp C j b ∈ (gateAt C j).inputs := by
    cases b
    · rw [inp_false, hxy]; simp
    · rw [inp_true, hxy]; simp
  exact ⟨hm, hC.2.1 j hj _ hm⟩

theorem Rr_inp {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : OrG C j)
    (b : Bool) : Rr n C (inp C j b) (n + j) := by
  obtain ⟨hm, hlt⟩ := inp_mem hC j hj.1 b
  exact Relation.ReflTransGen.single ⟨hlt, j, rfl, hj.1, hj.2, hm⟩

theorem Rr_tail {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (x w : ℕ)
    (h : Rr n C x w) : x = w ∨ ∃ j b, OrG C j ∧ w = n + j ∧ Rr n C x (inp C j b) := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨u, hu, _, rj, hw, hrj, hop, hmem⟩
  · exact Or.inl h1.symm
  · obtain ⟨b, hb⟩ := inp_cases hC rj hrj u hmem
    exact Or.inr ⟨rj, b, ⟨hrj, hop⟩, hw, by rw [← hb]; exact hu⟩

theorem Rr_and {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : AndG C j)
    (x : ℕ) (h : Rr n C x (n + j)) : x = n + j := by
  rcases Rr_tail hC x (n + j) h with h1 | ⟨j', b, hj', hw, _⟩
  · exact h1
  · exfalso
    have e : j = j' := by omega
    subst e
    have h2 := hj'.2
    rw [hj.2] at h2
    exact GateOp.noConfusion h2

theorem Rr_input {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (w : ℕ) (hw : w < n)
    (x : ℕ) (h : Rr n C x w) : x = w := by
  rcases Rr_tail hC x w h with h1 | ⟨j', b, _, hw', _⟩
  · exact h1
  · omega

theorem FMG {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) (Good : ℕ → Prop)
    (w0 w : ℕ) (h : Rr n C w0 w) (h0 : Good w0) (h1 : ¬ Good w) :
    ∃ jo b, OrG C jo ∧ Rr n C (n + jo) w ∧ Rr n C w0 (inp C jo b) ∧ Good (inp C jo b) ∧
      ¬ Good (n + jo) := by
  unfold Rr at h
  revert h1
  induction h with
  | refl => intro h1; exact absurd h0 h1
  | @tail b c hab hbc ih =>
    intro h1
    by_cases hb : Good b
    · obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc
      subst hc
      obtain ⟨bb, hbb⟩ := inp_cases hC rj hrj b hmem
      refine ⟨rj, bb, ⟨hrj, hop⟩, Rr_refl n C _, ?_, ?_, h1⟩
      · rw [← hbb]; exact hab
      · rw [← hbb]; exact hb
    · obtain ⟨jo, bo, h2, h3, h4, h5, h6⟩ := ih hb
      exact ⟨jo, bo, h2, Relation.ReflTransGen.tail h3 hbc, h4, h5, h6⟩

def Bd {X : Type} (P : X → Prop) (k : ℕ) : Prop :=
  ∀ S : Finset X, (∀ e ∈ S, P e) → S.card ≤ k

theorem Bd_mono {X : Type} {P Q : X → Prop} {k : ℕ} (h : ∀ e, P e → Q e) (hQ : Bd Q k) :
    Bd P k :=
  fun S hS => hQ S (fun e he => h e (hS e he))

theorem Bd_le {X : Type} {P : X → Prop} {k k' : ℕ} (h : k ≤ k') (hP : Bd P k) : Bd P k' :=
  fun S hS => (hP S hS).trans h

theorem Bd_or {X : Type} {P Q : X → Prop} {b c : ℕ} (hP : Bd P b) (hQ : Bd Q c) :
    Bd (fun e => P e ∨ Q e) (b + c) := by
  classical
  intro S hS
  have h1 := hP (S.filter (fun e => P e)) (fun e he => (Finset.mem_filter.mp he).2)
  have h2 := hQ (S.filter (fun e => ¬ P e)) (fun e he => by
    have h := Finset.mem_filter.mp he
    rcases hS e h.1 with h' | h'
    · exact absurd h' h.2
    · exact h')
  have h3 := Finset.card_filter_add_card_filter_not (s := S) (fun e => P e)
  omega

theorem Bd_charge {X κ : Type} (K : Finset κ) (Ch : κ → X → Prop) (k : ℕ)
    (hf : ∀ key ∈ K, Bd (Ch key) k) : Bd (fun e => ∃ key ∈ K, Ch key e) (k * K.card) := by
  classical
  intro S hS
  have hsub : S ⊆ K.biUnion (fun key => S.filter (fun e => Ch key e)) := by
    intro e he
    obtain ⟨key, hk, hc⟩ := hS e he
    exact Finset.mem_biUnion.mpr ⟨key, hk, Finset.mem_filter.mpr ⟨he, hc⟩⟩
  calc S.card ≤ (K.biUnion (fun key => S.filter (fun e => Ch key e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ key ∈ K, (S.filter (fun e => Ch key e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _key ∈ K, k := Finset.sum_le_sum (fun key hk =>
        hf key hk _ (fun e he => (Finset.mem_filter.mp he).2))
    _ = k * K.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

def ChU {α β : Type} (PA : α → Prop) (PB : β → Prop) (a : α) (b : β) : Prop :=
  PA a ∧ (∀ a', PA a' → a' = a) ∧ PB b ∧ (∀ b', PB b' → b' = b)

theorem Bd_U {α β : Type} (PA : α → Prop) (PB : β → Prop) :
    Bd (fun e : α × β => ChU PA PB e.1 e.2) 1 := by
  intro S hS
  refine Finset.card_le_one.mpr ?_
  intro e he e' he'
  obtain ⟨h1, _, h3, _⟩ := hS e he
  obtain ⟨_, h2', _, h4'⟩ := hS e' he'
  exact Prod.ext (h2' _ h1) (h4' _ h3)

def ChM {α β : Type} (Cmp : α → β → Prop) (L0 L1 : β → Prop) (a : α) (b : β) : Prop :=
  L0 b ∧ (∀ y, L0 y → y = b) ∧ L1 b ∧ (∃ y, L1 y ∧ y ≠ b) ∧ ∀ y, L1 y → Cmp a y

def No4 {α β : Type} (Cmp : α → β → Prop) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' → ¬ (Cmp a b ∧ Cmp a' b ∧ Cmp a b' ∧ Cmp a' b')

theorem No4_swap {α β : Type} {Cmp : α → β → Prop} (h : No4 Cmp) : No4 (fun b a => Cmp a b) := by
  intro b b' a a' hb ha hh
  exact h a a' b b' ha hb ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩

theorem Bd_M {X α β : Type} (fa : X → α) (fb : X → β)
    (hinj : ∀ e e' : X, fa e = fa e' → fb e = fb e' → e = e') (Cmp : α → β → Prop)
    (h4 : No4 Cmp) (L0 L1 : β → Prop) :
    Bd (fun e : X => ChM Cmp L0 L1 (fa e) (fb e)) 1 := by
  intro S hS
  refine Finset.card_le_one.mpr ?_
  intro e he e' he'
  obtain ⟨h1, _, h3, ⟨y, hy, hne⟩, h5⟩ := hS e he
  obtain ⟨_, h2', h3', _, h5'⟩ := hS e' he'
  have hb : fb e = fb e' := h2' _ h1
  refine hinj e e' ?_ hb
  by_contra hne2
  refine h4 (fa e) (fa e') (fb e) y hne2 (Ne.symm hne) ⟨h5 _ h3, ?_, h5 _ hy, h5' _ hy⟩
  rw [hb]
  exact h5' _ h3'

theorem card_le_of_maps {X Y : Type} (S : Finset X) (f : X → Y)
    (hinj : ∀ e ∈ S, ∀ e' ∈ S, f e = f e' → e = e') (T : Set Y) (hfin : T.Finite) (k : ℕ)
    (hT : T.ncard ≤ k) (hmem : ∀ e ∈ S, f e ∈ T) : S.card ≤ k := by
  classical
  have h1 : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => hinj e he e' he' h)
  have h2 : ((S.image f : Finset Y) : Set Y) ⊆ T := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
    exact hmem e he
  have h3 := Set.ncard_le_ncard h2 hfin
  rw [Set.ncard_coe_finset] at h3
  omega

theorem card_le_two_of_bool {X : Type} (S : Finset X) (f : X → Bool)
    (hinj : ∀ e ∈ S, ∀ e' ∈ S, f e = f e' → e = e') : S.card ≤ 2 := by
  classical
  have h1 : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (fun e he e' he' h => hinj e he e' he' h)
  have h2 : (S.image f).card ≤ (Finset.univ : Finset Bool).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have h3 : (Finset.univ : Finset Bool).card = 2 := by simp
  omega

theorem card_le_prod {X Y : Type} (S : Finset X) (f : X → Y) (a b : ℕ)
    (himg : ∀ T : Finset Y, (∀ y ∈ T, ∃ e ∈ S, f e = y) → T.card ≤ a)
    (hfib : ∀ y, ∀ T : Finset X, (∀ e ∈ T, e ∈ S ∧ f e = y) → T.card ≤ b) : S.card ≤ b * a := by
  classical
  have h1 : (S.image f).card ≤ a := himg _ (fun y hy => by
    obtain ⟨e, he, h⟩ := Finset.mem_image.mp hy
    exact ⟨e, he, h⟩)
  have h2 := Finset.card_le_mul_card_image (f := f) S b (fun y _ =>
    hfib y _ (fun e he => by
      have h := Finset.mem_filter.mp he
      exact ⟨h.1, h.2⟩))
  calc S.card ≤ b * (S.image f).card := h2
    _ ≤ b * a := Nat.mul_le_mul_left b h1

def Lb (n : ℕ) (C : Circuit) {β : Type} (φ : ℕ → β → Prop) (w : ℕ) (y : β) : Prop :=
  ∃ j, Rr n C (n + j) w ∧ φ j y

theorem Lb_mono {n : ℕ} {C : Circuit} {β : Type} {φ : ℕ → β → Prop} {a b : ℕ} {y : β}
    (h : Rr n C a b) (hl : Lb n C φ a y) : Lb n C φ b y := by
  obtain ⟨j, hj, hp⟩ := hl
  exact ⟨j, Rr_trans hj h, hp⟩

theorem Lb_self {n : ℕ} {C : Circuit} {β : Type} {φ : ℕ → β → Prop} {j : ℕ} {y : β}
    (h : φ j y) : Lb n C φ (n + j) y :=
  ⟨j, Rr_refl n C _, h⟩

theorem Lb_and {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {β : Type}
    {φ : ℕ → β → Prop} {j : ℕ} (hj : AndG C j) {y : β} (h : Lb n C φ (n + j) y) : φ j y := by
  obtain ⟨j', hj', hp⟩ := h
  have e := Rr_and hC j hj _ hj'
  have e2 : j' = j := by omega
  rw [← e2]
  exact hp

theorem FM3 {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {β : Type}
    (φ : ℕ → β → Prop) (w0 w : ℕ) (h : Rr n C w0 w) (y0 : β) :
    (∀ y, Lb n C φ w y → y = y0) ∨ (∃ y, Lb n C φ w0 y ∧ y ≠ y0) ∨
    ∃ jo b, OrG C jo ∧ Rr n C (n + jo) w ∧ Rr n C w0 (inp C jo b) ∧
      (∀ y, Lb n C φ (inp C jo b) y → y = y0) ∧ ∃ y, Lb n C φ (n + jo) y ∧ y ≠ y0 := by
  by_cases ha : ∀ y, Lb n C φ w y → y = y0
  · exact Or.inl ha
  by_cases hb : ∃ y, Lb n C φ w0 y ∧ y ≠ y0
  · exact Or.inr (Or.inl hb)
  refine Or.inr (Or.inr ?_)
  have h0 : ∀ y, Lb n C φ w0 y → y = y0 := by
    intro y hy
    by_contra hne
    exact hb ⟨y, hy, hne⟩
  obtain ⟨jo, b, h2, h3, h4, h5, h6⟩ := FMG hC (fun v => ∀ y, Lb n C φ v y → y = y0) w0 w h h0 ha
  refine ⟨jo, b, h2, h3, h4, h5, ?_⟩
  by_contra hne
  apply h6
  intro y hy
  by_contra hne2
  exact hne ⟨y, hy, hne2⟩

-- fragment f02_sib
section


theorem a07_key (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M))
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

theorem a07_card_aux {α : Type} [Finite α] (S : Set α)
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

theorem l2407 : ∀ (N M : ℕ) (I : Fin N → Fin M → Prop) (L : Set (Fin M)), (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → {p : Fin N | 3 ≤ {l : Fin M | l ∈ L ∧ I p l}.ncard ∧ ∃ z : Fin N, L ⊆ {l2 : Fin M | I p l2 ∨ I z l2}}.ncard ≤ 2 := by
  intro N M I L H
  apply a07_card_aux
  intro q hq
  obtain ⟨-, z, hz⟩ := hq
  refine ⟨z, ?_⟩
  intro p hp hpq
  obtain ⟨hp3, -⟩ := hp
  exact a07_key N M I L H p q z hpq hp3 hz


end

section


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- One upward step along an OR gate. -/
def a10_stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

/-- The pairs having a wire above the point whose shadow has two points, all on the line. -/
def a10_Bp (N M : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop) (R : ℕ → ℕ → Prop)
    (ex : Fin N × Fin M) : Prop :=
  ∃ w, R (pw ex.1) w ∧ (∀ q : Fin N, R (pw q) w → I q ex.2) ∧
    2 ≤ {r : Fin N | R (pw r) w}.ncard

theorem a10_gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  have h : gateAt C j = C.gates[j] := by
    unfold gateAt
    simp [List.getD_eq_getElem?_getD, hj]
  rw [h]
  exact List.getElem_mem hj

theorem a10_two_inputs (l : List ℕ) (hl : l.length = 2) (b : ℕ) (hb : b ∈ l) :
    b = l.getD 0 0 ∨ b = l.getD 1 0 := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hl
  · simp at hl
  · simpa using hb
  · simp at hl

theorem a10_base (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ) (hpw : Function.Injective pw)
    (hpn : ∀ p2 : Fin N, pw p2 < n) (r p : Fin N)
    (h : Relation.ReflTransGen (a10_stp n C) (pw r) (pw p)) : r = p := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨b, _, hs⟩
  · exact (hpw h1).symm
  · obtain ⟨_, rj, hrj, _⟩ := hs
    have := hpn p
    omega

theorem a10_key (n N : ℕ) (C : Circuit) (pw : Fin N → ℕ)
    (hlen : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpw : Function.Injective pw) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (R : ℕ → ℕ → Prop) (hR : R = Relation.ReflTransGen (a10_stp n C))
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
    have e1 : a = p := a10_base n N C pw hpw hpn a p ha
    have e2 : b = p := a10_base n N C pw hpw hpn b p hb
    exact hab (e1.trans e2.symm)
  | @tail b c hab hbc ih =>
    intro h2
    by_cases hb : 2 ≤ {r : Fin N | Relation.ReflTransGen (a10_stp n C) (pw r) b}.ncard
    · obtain ⟨jo, h1, h3, h4, h5, h6⟩ := ih hb
      exact ⟨jo, h1, h3, fun x hx => (h4 x hx).tail hbc, h5, h6⟩
    · have hbc2 := hbc
      obtain ⟨_, rj, hc, hrj, hop, hmem⟩ := hbc2
      subst hc
      have hm : gateAt C rj ∈ C.gates := a10_gate_mem C rj hrj
      have hl : (gateAt C rj).inputs.length = 2 := hlen _ hm
      have huniq : ∀ q : Fin N, Relation.ReflTransGen (a10_stp n C) (pw q) b → q = p := by
        intro q hq
        by_contra hne
        apply hb
        have hsub : ({q, p} : Set (Fin N)) ⊆
            {r : Fin N | Relation.ReflTransGen (a10_stp n C) (pw r) b} := by
          intro r hr
          rcases Set.mem_insert_iff.mp hr with h | h
          · rw [h]; exact hq
          · rw [Set.mem_singleton_iff.mp h]; exact hab
        calc 2 = ({q, p} : Set (Fin N)).ncard := (Set.ncard_pair hne).symm
          _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hcase : b = (gateAt C rj).inputs.getD 0 0 ∨ b = (gateAt C rj).inputs.getD 1 0 :=
        a10_two_inputs _ hl b hmem
      refine ⟨rj, hrj, hop, fun x hx => hx, h2, ?_⟩
      rcases hcase with h0 | h1
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (a10_stp n C) (pw p) ((gateAt C rj).inputs.getD 0 0)
          rw [← h0]; exact hab
        · intro q hq
          apply huniq q
          rw [h0]; exact hq
      · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
        · show Relation.ReflTransGen (a10_stp n C) (pw p) ((gateAt C rj).inputs.getD 1 0)
          rw [← h1]; exact hab
        · intro q hq
          apply huniq q
          rw [h1]; exact hq

theorem a10_leafR (n : ℕ) (C : Circuit) (R : ℕ → ℕ → Prop) (t : ℕ) (L : List (ℕ × ℕ))
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

theorem a10_final {α : Type} [Finite α] (PA PX : α → Prop) (k : ℕ) (B : Set α) (hB : B.ncard ≤ k)
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

theorem a10_sib_main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard := by
  intro n N M pw lw I C hAO hpw hlw hne hpn hln hK hsound R hR T hT hread
  subst hT
  have hlen := hAO.2.2
  have hBex : ∀ ex : Fin N × Fin M, a10_Bp N M pw I R ex → ∃ y : ℕ × Fin 2,
      (y.1 < C.gates.length ∧ (gateAt C y.1).op = GateOp.or) ∧
      2 ≤ {r : Fin N | R (pw r) (n + y.1)}.ncard ∧
      (∀ q : Fin N, R (pw q) (n + y.1) → I q ex.2) ∧
      R (pw ex.1) ((gateAt C y.1).inputs.getD y.2.val 0) ∧
      ∀ q : Fin N, R (pw q) ((gateAt C y.1).inputs.getD y.2.val 0) → q = ex.1 := by
    rintro ex ⟨w, hw, hsh, h2⟩
    obtain ⟨jo, h1, h3, h4, h5, i, h6, h7⟩ := a10_key n N C pw hlen hpw hpn R hR ex.1 w hw h2
    exact ⟨(jo, i), ⟨h1, h3⟩, h5, fun q hq => hsh q (h4 _ hq), h6, h7⟩
  choose! f hf using hBex
  have hO : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun jo h => h.1)
  have hBcard : {ex : Fin N × Fin M | a10_Bp N M pw I R ex}.ncard ≤
      2 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard := by
    have h1 : {ex : Fin N × Fin M | a10_Bp N M pw I R ex}.ncard ≤
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
  refine a10_final _ _ _ {ex : Fin N × Fin M | a10_Bp N M pw I R ex} hBcard ?_
  intro a ha hx
  obtain ⟨L7, ⟨j7, La7, Lb7, hj7, hop7, hR7, hTa, hTb, hL⟩, hvars, hcp, hcl, g8, hg8, hg8p,
    hsh, h2⟩ := hx
  subst hL
  have hRg : R g8.2 g8.1 := by
    rcases List.mem_append.mp hg8 with h | h
    · exact a10_leafR n C R _ La7 hTa g8 h
    · exact a10_leafR n C R _ Lb7 hTb g8 h
  rw [hg8p] at hRg
  exact ⟨g8.1, hRg, hsh, h2⟩

theorem a10_l2409 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 2 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ex : Fin N × Fin M | I ex.1 ex.2 ∧ ¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ex.1 ∨ g7.2 = lw ex.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ex.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ex.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ex.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ex.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard}.ncard :=
  a10_sib_main_aux

theorem a10_two_sided_swap_card {α β : Type} (P : α × β → Prop) (P' : β × α → Prop)
    (h : ∀ a b, P' (b, a) ↔ P (a, b)) :
    {e : β × α | P' e}.ncard = {e : α × β | P e}.ncard := by
  have himg : Prod.swap '' {e : α × β | P e} = {e : β × α | P' e} := by
    ext ⟨b, a⟩
    constructor
    · intro hm
      obtain ⟨⟨x, y⟩, hx, hxy⟩ := (Set.mem_image _ _ _).mp hm
      have h3 : y = b ∧ x = a := Prod.mk.inj hxy
      rw [← h3.1, ← h3.2]
      show P' (y, x)
      exact (h x y).mpr hx
    · intro hm
      exact (Set.mem_image _ _ _).mpr ⟨(a, b), (h a b).mp hm, rfl⟩
  rw [← himg]
  exact Set.ncard_image_of_injective _ Prod.swap_injective

theorem a10_two_sided_combine {α β : Type} [Finite α] [Finite β] (S A B : α × β → Prop)
    (S' A' : β × α → Prop) (k : ℕ)
    (hS : ∀ a b, S' (b, a) ↔ S (a, b))
    (hB : ∀ a b, S (a, b) → (A' (b, a) ↔ B (a, b)))
    (h1 : {e : α × β | S e}.ncard ≤ 2 * k + {e : α × β | S e ∧ ¬ A e}.ncard)
    (h2 : {e : β × α | S' e}.ncard ≤ 2 * k + {e : β × α | S' e ∧ ¬ A' e}.ncard) :
    {e : α × β | S e}.ncard ≤ 4 * k + {e : α × β | S e ∧ ¬ A e ∧ ¬ B e}.ncard := by
  have e1 : {e : β × α | S' e}.ncard = {e : α × β | S e}.ncard := a10_two_sided_swap_card S S' hS
  have e2 : {e : β × α | S' e ∧ ¬ A' e}.ncard = {e : α × β | S e ∧ ¬ B e}.ncard := by
    refine a10_two_sided_swap_card (fun e => S e ∧ ¬ B e) (fun e => S' e ∧ ¬ A' e) ?_
    intro a b
    constructor
    · intro hh
      exact ⟨(hS a b).mp hh.1, fun hb => hh.2 ((hB a b ((hS a b).mp hh.1)).mpr hb)⟩
    · intro hh
      exact ⟨(hS a b).mpr hh.1, fun ha => hh.2 ((hB a b hh.1).mp ha)⟩
  have hU := Set.ncard_union_add_ncard_inter {e : α × β | S e ∧ ¬ A e} {e : α × β | S e ∧ ¬ B e}
  have hsub1 : ({e : α × β | S e ∧ ¬ A e} ∪ {e : α × β | S e ∧ ¬ B e}).ncard
      ≤ {e : α × β | S e}.ncard := by
    apply Set.ncard_le_ncard
    · intro e he
      rcases he with hh | hh
      · exact hh.1
      · exact hh.1
    · exact Set.toFinite _
  have hsub2 : ({e : α × β | S e ∧ ¬ A e} ∩ {e : α × β | S e ∧ ¬ B e}).ncard
      ≤ {e : α × β | S e ∧ ¬ A e ∧ ¬ B e}.ncard := by
    apply Set.ncard_le_ncard
    · intro e he
      exact ⟨he.1.1, he.1.2, he.2.2⟩
    · exact Set.toFinite _
  rw [e1, e2] at h2
  omega

theorem l2410 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 4 * {jo : ℕ | jo < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jo).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard + {ey : Fin N × Fin M | I ey.1 ey.2 ∧ (¬ ∃ L7 : List (ℕ × ℕ), (∃ (j7 : ℕ) (La7 Lb7 : List (ℕ × ℕ)), j7 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j7) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 0 0) La7 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j7).inputs.getD 1 0) Lb7 ∧ L7 = La7 ++ Lb7) ∧ (∀ g7 ∈ L7, g7.2 = pw ey.1 ∨ g7.2 = lw ey.2) ∧ (L7.filter (fun e7 => decide (e7.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L7.filter (fun f7 => decide (f7.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g8 ∈ L7, g8.2 = pw ey.1 ∧ (∀ q8 : Fin N, R (pw q8) g8.1 → I q8 ey.2) ∧ 2 ≤ {r8 : Fin N | R (pw r8) g8.1}.ncard) ∧ ¬ ∃ L9 : List (ℕ × ℕ), (∃ (j9 : ℕ) (La9 Lb9 : List (ℕ × ℕ)), j9 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j9) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 0 0) La9 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j9).inputs.getD 1 0) Lb9 ∧ L9 = La9 ++ Lb9) ∧ (∀ g9 ∈ L9, g9.2 = pw ey.1 ∨ g9.2 = lw ey.2) ∧ (L9.filter (fun e9 => decide (e9.2 = pw ey.1))).length ∈ ({1, 2} : Finset ℕ) ∧ (L9.filter (fun f9 => decide (f9.2 = lw ey.2))).length ∈ ({1, 2} : Finset ℕ) ∧ ∃ g10 ∈ L9, g10.2 = lw ey.2 ∧ (∀ q10 : Fin M, R (lw q10) g10.1 → I ey.1 q10) ∧ 2 ≤ {r10 : Fin M | R (lw r10) g10.1}.ncard}.ncard := by
  intro n N M pw lw I C hAO hpi hli hne hpn hln hK hS R hR T hT hTree
  have h1 := a10_l2409 n N M pw lw I C hAO hpi hli hne hpn hln hK hS R hR T hT hTree
  have h2 := a10_l2409 n M N lw pw (fun l p => I p l) C hAO hli hpi
    (fun p l => (hne l p).symm) hln hpn
    (fun p4 p5 l4 l5 hp hl h => hK l4 l5 p4 p5 hl hp ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩)
    (fun P Y hP hY hno => by
      have e : (P.image lw ∪ Y.image pw) = (Y.image pw ∪ P.image lw) := Finset.union_comm _ _
      rw [e]
      exact hS Y P hY hP (fun p hp l hl => hno l hl p hp))
    R hR T hT
    (fun p6 l6 h => by
      obtain ⟨L, ht, hall, hf1, hf2⟩ := hTree l6 p6 h
      exact ⟨L, ht, fun g hg => (hall g hg).symm, hf2, hf1⟩)
  refine a10_two_sided_combine _ _ _ _ _ _ ?_ ?_ h1 h2
  · intro a b
    exact Iff.rfl
  · intro a b _
    constructor
    · intro hh
      obtain ⟨L, ht, hall, hf1, hf2, hg⟩ := hh
      exact ⟨L, ht, fun g hg' => (hall g hg').symm, hf2, hf1, hg⟩
    · intro hh
      obtain ⟨L, ht, hall, hf1, hf2, hg⟩ := hh
      exact ⟨L, ht, fun g hg' => (hall g hg').symm, hf2, hf1, hg⟩


end

-- fragment f03_f3
def ChF3 (n : ℕ) (C : Circuit) {K1 K2 : ℕ} (yw : Fin K2 → ℕ) (Cmp : Fin K1 → Fin K2 → Prop)
    (key : ℕ × Bool) (a : Fin K1) (y : Fin K2) : Prop :=
  Rr n C (yw y) (inp C key.1 key.2) ∧ Cmp a y ∧
  {t : Fin K2 | Rr n C (yw t) (inp C key.1 key.2) ∧ Cmp a t}.ncard ≤ 2 ∧
  3 ≤ {t : Fin K2 | Rr n C (yw t) (n + key.1) ∧ Cmp a t}.ncard ∧
  ∃ z : Fin K1, ∀ t, Rr n C (yw t) (n + key.1) → Cmp a t ∨ Cmp z t

theorem F3_exists {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {K1 K2 : ℕ}
    (yw : Fin K2 → ℕ) (hinj : Function.Injective yw) (hlt : ∀ y, yw y < n)
    (Cmp : Fin K1 → Fin K2 → Prop) (d : ℕ) (a : Fin K1) (y : Fin K2)
    (h : Rr n C (yw y) d) (hc : Cmp a y)
    (h3 : 3 ≤ {t : Fin K2 | Rr n C (yw t) d ∧ Cmp a t}.ncard)
    (z : Fin K1) (hz : ∀ t, Rr n C (yw t) d → Cmp a t ∨ Cmp z t) :
    ∃ jo b, OrG C jo ∧ ChF3 n C yw Cmp (jo, b) a y := by
  have h0 : {t : Fin K2 | Rr n C (yw t) (yw y) ∧ Cmp a t}.ncard ≤ 2 := by
    have hsub : {t : Fin K2 | Rr n C (yw t) (yw y) ∧ Cmp a t} ⊆ {y} := by
      intro t ht
      exact hinj (Rr_input hC _ (hlt y) _ ht.1)
    have h := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at h
    omega
  obtain ⟨jo, b, h2, h3', h4, h5, h6⟩ := FMG hC
    (fun v => {t : Fin K2 | Rr n C (yw t) v ∧ Cmp a t}.ncard ≤ 2) (yw y) d h h0
    (not_le.mpr (by omega))
  have h6' := not_le.mp h6
  refine ⟨jo, b, h2, h4, hc, h5, ?_, z, fun t ht => hz t (Rr_trans ht h3')⟩
  show 3 ≤ {t : Fin K2 | Rr n C (yw t) (n + jo) ∧ Cmp a t}.ncard
  omega

theorem F3_fiber {n : ℕ} {C : Circuit} {X : Type} {K1 K2 : ℕ} (fa : X → Fin K1) (fb : X → Fin K2)
    (hinj : ∀ e e' : X, fa e = fa e' → fb e = fb e' → e = e')
    (yw : Fin K2 → ℕ) (Cmp : Fin K1 → Fin K2 → Prop) (h4 : No4 Cmp) (key : ℕ × Bool) :
    Bd (fun e : X => ChF3 n C yw Cmp key (fa e) (fb e)) 4 := by
  intro S hS
  have hm2 := l2407 K1 K2 Cmp {t : Fin K2 | Rr n C (yw t) (n + key.1)} h4
  have hh : S.card ≤ 2 * 2 := by
    refine card_le_prod S fa 2 2 ?_ ?_
    · intro T hT
      refine card_le_of_maps T id (fun e _ e' _ h => h) _ (Set.toFinite _) 2 hm2 ?_
      intro a ha
      obtain ⟨e, he, rfl⟩ := hT a ha
      obtain ⟨_, _, _, h3, z, hz⟩ := hS e he
      exact ⟨h3, z, fun t ht => hz t ht⟩
    · intro a T hT
      rcases T.eq_empty_or_nonempty with h | ⟨e0, he0⟩
      · simp [h]
      · obtain ⟨he0S, hae0⟩ := hT e0 he0
        have hk := (hS e0 he0S).2.2.1
        rw [hae0] at hk
        refine card_le_of_maps T fb (fun e he e' he' h =>
          hinj e e' ((hT e he).2.trans (hT e' he').2.symm) h) _ (Set.toFinite _) 2 hk ?_
        intro e he
        obtain ⟨heS, hae⟩ := hT e he
        obtain ⟨h1, h2, _⟩ := hS e heS
        rw [hae] at h2
        exact ⟨h1, h2⟩
  omega

-- fragment f04_tree
def Tt (n : ℕ) (C : Circuit) (tt : ℕ) (tL : List (ℕ × ℕ)) : Prop :=
  ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → Rr n C qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (gateAt C qj).op = GateOp.and → Rr n C (n + qj) qt → Q ((gateAt C qj).inputs.getD 0 0) qL1 → Q ((gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL

theorem Tt_inv {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : Tt n C t L) :
    (∃ v, v < n ∧ Rr n C v t ∧ L = [(t, v)]) ∨
    (∃ j L1 L2, AndG C j ∧ Rr n C (n + j) t ∧ Tt n C (inp C j false) L1 ∧
      Tt n C (inp C j true) L2 ∧ L = L1 ++ L2) := by
  refine (h (fun t L => Tt n C t L ∧ ((∃ v, v < n ∧ Rr n C v t ∧ L = [(t, v)]) ∨
    (∃ j L1 L2, AndG C j ∧ Rr n C (n + j) t ∧ Tt n C (inp C j false) L1 ∧
      Tt n C (inp C j true) L2 ∧ L = L1 ++ L2))) ?_ ?_).2
  · intro qv qt hv hR
    exact ⟨fun Q h1 _ => h1 qv qt hv hR, Or.inl ⟨qv, hv, hR, rfl⟩⟩
  · intro qj qt L1 L2 hj hop hR h1 h2
    refine ⟨fun Q a b => b qj qt L1 L2 hj hop hR (h1.1 Q a b) (h2.1 Q a b),
      Or.inr ⟨qj, L1, L2, ⟨hj, hop⟩, hR, ?_, ?_, rfl⟩⟩
    · rw [inp_false]; exact h1.1
    · rw [inp_true]; exact h2.1

theorem Tt_pos {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : Tt n C t L) :
    1 ≤ L.length := by
  refine h (fun _ L => 1 ≤ L.length) ?_ ?_
  · intro qv qt _ _
    simp
  · intro qj qt L1 L2 _ _ _ h1 h2
    simp only [List.length_append]
    omega

theorem Tt_leafR {n : ℕ} {C : Circuit} {t : ℕ} {L : List (ℕ × ℕ)} (h : Tt n C t L) :
    ∀ g ∈ L, Rr n C g.2 g.1 := by
  refine h (fun _ L => ∀ g ∈ L, Rr n C g.2 g.1) ?_ ?_
  · intro qv qt _ hR g hg
    rw [List.mem_singleton] at hg
    rw [hg]
    exact hR
  · intro qj qt L1 L2 _ _ _ h1 h2 g hg
    rcases List.mem_append.mp hg with h | h
    · exact h1 g h
    · exact h2 g h

def cnt (q : ℕ) (L : List (ℕ × ℕ)) : ℕ := (L.filter (fun e => decide (e.2 = q))).length

theorem cnt_append (q : ℕ) (L1 L2 : List (ℕ × ℕ)) : cnt q (L1 ++ L2) = cnt q L1 + cnt q L2 := by
  simp [cnt]

theorem cnt_single_eq (q s : ℕ) : cnt q [(s, q)] = 1 := by
  simp [cnt]

theorem cnt_single_ne (q s p : ℕ) (h : p ≠ q) : cnt q [(s, p)] = 0 := by
  simp [cnt, h]

def LOK (wp wl : ℕ) (X Y : ℕ → Prop) (L : List (ℕ × ℕ)) : Prop :=
  ∀ g ∈ L, (g.2 = wp ∧ X g.1) ∨ (g.2 = wl ∧ Y g.1)

theorem LOK_left {wp wl : ℕ} {X Y : ℕ → Prop} {L1 L2 : List (ℕ × ℕ)}
    (h : LOK wp wl X Y (L1 ++ L2)) : LOK wp wl X Y L1 :=
  fun g hg => h g (List.mem_append.mpr (Or.inl hg))

theorem LOK_right {wp wl : ℕ} {X Y : ℕ → Prop} {L1 L2 : List (ℕ × ℕ)}
    (h : LOK wp wl X Y (L1 ++ L2)) : LOK wp wl X Y L2 :=
  fun g hg => h g (List.mem_append.mpr (Or.inr hg))

theorem cnt_total {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (L : List (ℕ × ℕ))
    (h : LOK wp wl X Y L) : cnt wp L + cnt wl L = L.length := by
  induction L with
  | nil => simp [cnt]
  | cons g L ih =>
    have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have e1 : cnt wp (g :: L) = cnt wp [g] + cnt wp L := cnt_append wp [g] L
    have e2 : cnt wl (g :: L) = cnt wl [g] + cnt wl L := cnt_append wl [g] L
    have hg := h g (List.mem_cons_self)
    have e3 : cnt wp [g] + cnt wl [g] = 1 := by
      obtain ⟨g1, g2⟩ := g
      rcases hg with ⟨hh, _⟩ | ⟨hh, _⟩
      · simp only at hh
        subst hh
        rw [cnt_single_eq, cnt_single_ne _ _ _ hne]
      · simp only at hh
        subst hh
        rw [cnt_single_eq, cnt_single_ne _ _ _ (Ne.symm hne)]
    simp only [List.length_cons]
    omega

theorem D1 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) {t : ℕ}
    {L : List (ℕ × ℕ)} (h : Tt n C t L) (hl : L.length = 1) (hk : LOK wp wl X Y L) :
    (X t ∧ cnt wp L = 1 ∧ cnt wl L = 0) ∨ (Y t ∧ cnt wp L = 0 ∧ cnt wl L = 1) := by
  rcases Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, _, _, h1, h2, hL⟩
  · subst hL
    rcases hk (t, v) (by simp) with ⟨hh, hx⟩ | ⟨hh, hy⟩
    · simp only at hh hx
      subst hh
      exact Or.inl ⟨hx, cnt_single_eq _ _, cnt_single_ne _ _ _ hne⟩
    · simp only at hh hy
      subst hh
      exact Or.inr ⟨hy, cnt_single_ne _ _ _ (Ne.symm hne), cnt_single_eq _ _⟩
  · exfalso
    have p1 := Tt_pos h1
    have p2 := Tt_pos h2
    rw [hL, List.length_append] at hl
    omega

theorem D2 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) {t : ℕ}
    {L : List (ℕ × ℕ)} (h : Tt n C t L) (hl : L.length = 2) (hk : LOK wp wl X Y L) :
    ∃ j c, AndG C j ∧ Rr n C (n + j) t ∧
      ((X (inp C j c) ∧ X (inp C j (!c)) ∧ cnt wp L = 2 ∧ cnt wl L = 0) ∨
       (X (inp C j c) ∧ Y (inp C j (!c)) ∧ cnt wp L = 1 ∧ cnt wl L = 1) ∨
       (Y (inp C j c) ∧ Y (inp C j (!c)) ∧ cnt wp L = 0 ∧ cnt wl L = 2)) := by
  rcases Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, hj, hR, h1, h2, hL⟩
  · exfalso
    rw [hL] at hl
    simp at hl
  · subst hL
    have p1 := Tt_pos h1
    have p2 := Tt_pos h2
    rw [List.length_append] at hl
    have e1 := cnt_append wp L1 L2
    have e2 := cnt_append wl L1 L2
    rcases D1 hne h1 (by omega) (LOK_left hk) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · rcases D1 hne h2 (by omega) (LOK_right hk) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
      · exact ⟨j, false, hj, hR, Or.inl ⟨a1, b1, by omega, by omega⟩⟩
      · exact ⟨j, false, hj, hR, Or.inr (Or.inl ⟨a1, b1, by omega, by omega⟩)⟩
    · rcases D1 hne h2 (by omega) (LOK_right hk) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
      · exact ⟨j, true, hj, hR, Or.inr (Or.inl ⟨b1, a1, by omega, by omega⟩)⟩
      · exact ⟨j, false, hj, hR, Or.inr (Or.inr ⟨a1, b1, by omega, by omega⟩)⟩

theorem D3 {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} {t : ℕ}
    {L : List (ℕ × ℕ)} (h : Tt n C t L) (hl : L.length = 3) (hk : LOK wp wl X Y L) :
    ∃ j c L1 L2, AndG C j ∧ Rr n C (n + j) t ∧ Tt n C (inp C j c) L1 ∧ Tt n C (inp C j (!c)) L2 ∧
      L1.length = 1 ∧ L2.length = 2 ∧ LOK wp wl X Y L1 ∧ LOK wp wl X Y L2 ∧
      cnt wp L = cnt wp L1 + cnt wp L2 ∧ cnt wl L = cnt wl L1 + cnt wl L2 := by
  rcases Tt_inv h with ⟨v, _, _, hL⟩ | ⟨j, L1, L2, hj, hR, h1, h2, hL⟩
  · exfalso
    rw [hL] at hl
    simp at hl
  · subst hL
    have p1 := Tt_pos h1
    have p2 := Tt_pos h2
    rw [List.length_append] at hl
    have e1 := cnt_append wp L1 L2
    have e2 := cnt_append wl L1 L2
    by_cases h11 : L1.length = 1
    · exact ⟨j, false, L1, L2, hj, hR, h1, h2, h11, by omega, LOK_left hk, LOK_right hk, e1, e2⟩
    · exact ⟨j, true, L2, L1, hj, hR, h2, h1, by omega, by omega, LOK_right hk, LOK_left hk,
        by omega, by omega⟩

def Sh2 (n : ℕ) (C : Circuit) (X Y : ℕ → Prop) : Prop :=
  ∃ jr b, AndG C jr ∧ Rr n C (n + jr) C.output ∧ X (inp C jr b) ∧ Y (inp C jr (!b))

def Sh3 (n : ℕ) (C : Circuit) (X Y Z : ℕ → Prop) : Prop :=
  ∃ jr b j c, AndG C jr ∧ Rr n C (n + jr) C.output ∧ X (inp C jr b) ∧ AndG C j ∧
    Rr n C (n + j) (inp C jr (!b)) ∧ Y (inp C j c) ∧ Z (inp C j (!c))

def ShBal (n : ℕ) (C : Circuit) (X Y Z W : ℕ → Prop) : Prop :=
  ∃ jr b j1 c1 j2 c2, AndG C jr ∧ Rr n C (n + jr) C.output ∧ AndG C j1 ∧
    Rr n C (n + j1) (inp C jr b) ∧ X (inp C j1 c1) ∧ Y (inp C j1 (!c1)) ∧ AndG C j2 ∧
    Rr n C (n + j2) (inp C jr (!b)) ∧ Z (inp C j2 c2) ∧ W (inp C j2 (!c2))

def ShCat (n : ℕ) (C : Circuit) (X Y Z W : ℕ → Prop) : Prop :=
  ∃ jr b j c j' c', AndG C jr ∧ Rr n C (n + jr) C.output ∧ X (inp C jr b) ∧ AndG C j ∧
    Rr n C (n + j) (inp C jr (!b)) ∧ Y (inp C j c) ∧ AndG C j' ∧
    Rr n C (n + j') (inp C j (!c)) ∧ Z (inp C j' c') ∧ W (inp C j' (!c'))

def Prim (n : ℕ) (C : Circuit) (X Y : ℕ → Prop) : Prop :=
  Sh2 n C X Y ∨ Sh3 n C X X Y ∨ Sh3 n C X Y Y ∨ ShBal n C X X Y Y ∨ ShBal n C X Y X Y ∨
    ShCat n C X X Y Y ∨ ShCat n C X Y X Y

theorem rootcase {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (jr : ℕ)
    (b : Bool) (hjr : AndG C jr) (hout : Rr n C (n + jr) C.output) (L1 L2 : List (ℕ × ℕ))
    (h1 : Tt n C (inp C jr b) L1) (h2 : Tt n C (inp C jr (!b)) L2)
    (hk1 : LOK wp wl X Y L1) (hk2 : LOK wp wl X Y L2)
    (hc : 1 ≤ cnt wp L1 + cnt wp L2 ∧ cnt wp L1 + cnt wp L2 ≤ 2)
    (hc' : 1 ≤ cnt wl L1 + cnt wl L2 ∧ cnt wl L1 + cnt wl L2 ≤ 2)
    (hlen : (L1.length = 1 ∧ L2.length = 1) ∨ (L1.length = 1 ∧ L2.length = 2) ∨
      (L1.length = 1 ∧ L2.length = 3) ∨ (L1.length = 2 ∧ L2.length = 2)) :
    Prim n C X Y ∨ Prim n C Y X := by
  rcases hlen with ⟨l1, l2⟩ | ⟨l1, l2⟩ | ⟨l1, l2⟩ | ⟨l1, l2⟩
  · rcases D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases D1 hne h2 l2 hk2 with ⟨hy, b2, b3⟩ | ⟨hy, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inl ⟨jr, b, hjr, hout, hx, hy⟩)
    · rcases D1 hne h2 l2 hk2 with ⟨hy, b2, b3⟩ | ⟨hy, b2, b3⟩
      · exact Or.inr (Or.inl ⟨jr, b, hjr, hout, hx, hy⟩)
      · exfalso; omega
  · obtain ⟨j, c, hj, hRj, hkind⟩ := D2 hne h2 l2 hk2
    rcases D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩)))
    · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, hjr, hout, hx, hj, hRj, ha, hb⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨jr, b, j, !c, hjr, hout, hx, hj, hRj, hb,
          by rw [Bool.not_not]; exact ha⟩))
      · exfalso; omega
  · obtain ⟨j, c, L3, L4, hj, hRj, h3, h4, l3, l4, hk3, hk4, e1, e2⟩ := D3 h2 l2 hk2
    obtain ⟨j', c', hj', hRj', hkind⟩ := D2 hne h4 l4 hk4
    rcases D1 hne h1 l1 hk1 with ⟨hx, a2, a3⟩ | ⟨hx, a2, a3⟩
    · rcases D1 hne h3 l3 hk3 with ⟨hy, d2, d3⟩ | ⟨hy, d2, d3⟩
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exfalso; omega
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
        · exfalso; omega
    · rcases D1 hne h3 l3 hk3 with ⟨hy, d2, d3⟩ | ⟨hy, d2, d3⟩
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exfalso; omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨jr, b, j, c, j', !c', hjr, hout, hx, hj, hRj, hy, hj', hRj', hb,
              by rw [Bool.not_not]; exact ha⟩))))))
        · exfalso; omega
      · rcases hkind with ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩ | ⟨ha, hb, b2, b3⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, hy, hj', hRj', ha, hb⟩))))))
        · exfalso; omega
        · exfalso; omega
  · obtain ⟨j1, c1, hj1, hRj1, hkind1⟩ := D2 hne h1 l1 hk1
    obtain ⟨j2, c2, hj2, hRj2, hkind2⟩ := D2 hne h2 l2 hk2
    rcases hkind1 with ⟨ha, hb, a2, a3⟩ | ⟨ha, hb, a2, a3⟩ | ⟨ha, hb, a2, a3⟩
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exfalso; omega
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩))))
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exfalso; omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩)))))
      · exfalso; omega
    · rcases hkind2 with ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩ | ⟨hc1, hd, b2, b3⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hRj1, ha, hb, hj2, hRj2, hc1, hd⟩))))
      · exfalso; omega
      · exfalso; omega

theorem prim_of_tree {n : ℕ} {C : Circuit} {wp wl : ℕ} {X Y : ℕ → Prop} (hne : wp ≠ wl) (jr : ℕ)
    (hjr : AndG C jr) (hout : Rr n C (n + jr) C.output) (La Lb : List (ℕ × ℕ))
    (h1 : Tt n C (inp C jr false) La) (h2 : Tt n C (inp C jr true) Lb)
    (hk : LOK wp wl X Y (La ++ Lb))
    (hc : cnt wp (La ++ Lb) = 1 ∨ cnt wp (La ++ Lb) = 2)
    (hc' : cnt wl (La ++ Lb) = 1 ∨ cnt wl (La ++ Lb) = 2) :
    Prim n C X Y ∨ Prim n C Y X := by
  have p1 := Tt_pos h1
  have p2 := Tt_pos h2
  have e1 := cnt_append wp La Lb
  have e2 := cnt_append wl La Lb
  have e3 := cnt_total hne (La ++ Lb) hk
  rw [List.length_append] at e3
  have hcases : (La.length = 1 ∧ Lb.length = 1) ∨ (La.length = 1 ∧ Lb.length = 2) ∨
      (La.length = 1 ∧ Lb.length = 3) ∨ (La.length = 2 ∧ Lb.length = 2) ∨
      (Lb.length = 1 ∧ La.length = 2) ∨ (Lb.length = 1 ∧ La.length = 3) := by omega
  rcases hcases with h | h | h | h | h | h
  · exact rootcase hne jr false hjr hout La Lb h1 h2 (LOK_left hk) (LOK_right hk)
      (by omega) (by omega) (Or.inl h)
  · exact rootcase hne jr false hjr hout La Lb h1 h2 (LOK_left hk) (LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inl h))
  · exact rootcase hne jr false hjr hout La Lb h1 h2 (LOK_left hk) (LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inl h)))
  · exact rootcase hne jr false hjr hout La Lb h1 h2 (LOK_left hk) (LOK_right hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inr h)))
  · exact rootcase hne jr true hjr hout Lb La h2 h1 (LOK_right hk) (LOK_left hk)
      (by omega) (by omega) (Or.inr (Or.inl h))
  · exact rootcase hne jr true hjr hout Lb La h2 h1 (LOK_right hk) (LOK_left hk)
      (by omega) (by omega) (Or.inr (Or.inr (Or.inl h)))

-- fragment f05_sys
def Sys (n : ℕ) (C : Circuit) (N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) : Prop :=
  PEqualNP.TopForm.IsAO2 n C ∧ Function.Injective pw ∧ Function.Injective lw ∧
  (∀ p, pw p < n) ∧ (∀ l, lw l < n) ∧ No4 I ∧
  (∀ P Y x, x ∈ P → Tr P Y (pw x)) ∧ (∀ P Y y, y ∈ Y → Tr P Y (lw y)) ∧
  (∀ P Y a b, Rr n C a b → Tr P Y a → Tr P Y b) ∧
  (∀ P Y j, AndG C j → Tr P Y (inp C j false) → Tr P Y (inp C j true) → Tr P Y (n + j)) ∧
  (∀ P Y, P.card ≤ 2 → Y.card ≤ 2 → Tr P Y C.output → ∃ x ∈ P, ∃ y ∈ Y, I x y)

theorem Sys_swap {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) :
    Sys n C M N lw pw (fun y x => I x y) (fun Y P w => Tr P Y w) := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  refine ⟨hC, hlw, hpw, hln, hpn, No4_swap h4, fun Y P y hy => htl P Y y hy,
    fun Y P x hx => htp P Y x hx, fun Y P a b h => htR P Y a b h,
    fun Y P j hj => htA P Y j hj, ?_⟩
  intro Y P hY hP h
  obtain ⟨x, hx, y, hy, hI⟩ := hsnd P Y hP hY h
  exact ⟨y, hy, x, hx, hI⟩

theorem tr_p {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {x : Fin N} {w : ℕ}
    (hx : x ∈ P) (h : Rr n C (pw x) w) : Tr P Y w := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h (htp P Y x hx)

theorem tr_l {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {y : Fin M} {w : ℕ}
    (hy : y ∈ Y) (h : Rr n C (lw y) w) : Tr P Y w := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h (htl P Y y hy)

theorem tr_R {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {a b : ℕ}
    (h : Rr n C a b) (ha : Tr P Y a) : Tr P Y b := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  exact htR P Y _ _ h ha

theorem tr_and {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} (hj : AndG C j)
    (c : Bool) (h1 : Tr P Y (inp C j c)) (h2 : Tr P Y (inp C j (!c))) : Tr P Y (n + j) := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  cases c
  · exact htA P Y j hj h1 h2
  · exact htA P Y j hj h2 h1

theorem snd22 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {x z : Fin N} {y t : Fin M} (h : Tr {x, z} {y, t} C.output) :
    I x y ∨ I x t ∨ I z y ∨ I z t := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x, z} {y, t} Finset.card_le_two Finset.card_le_two h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> tauto

theorem snd21 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {x z : Fin N} {y : Fin M} (h : Tr {x, z} {y} C.output) :
    I x y ∨ I z y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x, z} {y} Finset.card_le_two (by simp) h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl | rfl <;> rcases hy' with rfl <;> tauto

theorem snd12 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {x : Fin N} {y t : Fin M} (h : Tr {x} {y, t} C.output) :
    I x y ∨ I x t := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x} {y, t} (by simp) Finset.card_le_two h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx' hy'
  rcases hx' with rfl <;> rcases hy' with rfl | rfl <;> tauto

theorem snd11 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {x : Fin N} {y : Fin M} (h : Tr {x} {y} C.output) : I x y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  obtain ⟨x', hx', y', hy', hI⟩ := hsnd {x} {y} (by simp) (by simp) h
  simp only [Finset.mem_singleton] at hx' hy'
  rw [hx', hy'] at hI
  exact hI

noncomputable def andS (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)

noncomputable def orS (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)

theorem mem_andS {C : Circuit} {j : ℕ} : j ∈ andS C ↔ AndG C j := by
  unfold andS AndG
  simp only [Finset.mem_filter, Finset.mem_range]

theorem mem_orS {C : Circuit} {j : ℕ} : j ∈ orS C ↔ OrG C j := by
  unfold orS OrG
  simp only [Finset.mem_filter, Finset.mem_range]

theorem and_or_card {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) :
    (andS C).card + (orS C).card = C.gates.length := by
  classical
  have hd : Disjoint (andS C) (orS C) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (mem_andS.mp h1).2
    have a2 := (mem_orS.mp h2).2
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hu : andS C ∪ orS C = Finset.range C.gates.length := by
    ext j
    rw [Finset.mem_union, mem_andS, mem_orS, Finset.mem_range]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hj
      rcases hC.1 _ (gateAt_mem C j hj) with h | h
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, h⟩
  have h := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_range] at h
  omega

noncomputable def KA (C : Circuit) : Finset (ℕ × Bool) := (andS C) ×ˢ (Finset.univ : Finset Bool)

noncomputable def KO (C : Circuit) : Finset (ℕ × Bool) := (orS C) ×ˢ (Finset.univ : Finset Bool)

theorem mem_KA {C : Circuit} {key : ℕ × Bool} : key ∈ KA C ↔ AndG C key.1 := by
  unfold KA
  rw [Finset.mem_product, mem_andS]
  simp

theorem mem_KO {C : Circuit} {key : ℕ × Bool} : key ∈ KO C ↔ OrG C key.1 := by
  unfold KO
  rw [Finset.mem_product, mem_orS]
  simp

theorem card_KA (C : Circuit) : (KA C).card = 2 * (andS C).card := by
  unfold KA
  rw [Finset.card_product]
  simp
  omega

theorem card_KO (C : Circuit) : (KO C).card = 2 * (orS C).card := by
  unfold KO
  rw [Finset.card_product]
  simp
  omega

def PPr (n : ℕ) (C : Circuit) {K : ℕ} (xw : Fin K → ℕ) (a : ℕ) (x : Fin K) : Prop :=
  Rr n C (xw x) a ∧ ∀ x', Rr n C (xw x') a → x' = x

def GPf (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (w : ℕ) : Prop :=
  Rr n C (pw p) w ∧ ((∀ x, Rr n C (pw x) w → x = p) ∨ ∃ q, Rr n C (pw q) w ∧ ¬ I q l)

def GLf (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (w : ℕ) : Prop :=
  Rr n C (lw l) w ∧ ((∀ y, Rr n C (lw y) w → y = l) ∨ ∃ y, Rr n C (lw y) w ∧ ¬ I p y)

def Junk (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (x : Fin N) (t : Fin M) : Prop :=
  AndG C j ∧ ∃ c, Rr n C (pw x) (inp C j c) ∧ Rr n C (lw t) (inp C j (!c)) ∧ ¬ I x t

def phi2 (n : ℕ) (C : Circuit) {K : ℕ} (xw : Fin K → ℕ) (j : ℕ) (x : Fin K) : Prop :=
  AndG C j ∧ Rr n C (xw x) (inp C j false) ∧ Rr n C (xw x) (inp C j true)

def phiS (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (x : Fin N) : Prop :=
  ∃ t, Junk n C pw lw I j x t

def phiB (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  ∃ z, Junk n C pw lw I j z y

theorem junk_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {x : Fin N} {t : Fin M}
    (h : Junk n C pw lw I j x t) (hx : x ∈ P) (ht : t ∈ Y) : Tr P Y (n + j) := by
  obtain ⟨hj, c, h1, h2, _⟩ := h
  exact tr_and hS hj c (tr_p hS hx h1) (tr_l hS ht h2)

theorem phi2p_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {x : Fin N}
    (h : phi2 n C pw j x) (hx : x ∈ P) : Tr P Y (n + j) := by
  obtain ⟨hj, h1, h2⟩ := h
  exact tr_and hS hj false (tr_p hS hx h1) (tr_p hS hx h2)

theorem phi2l_tr {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {P : Finset (Fin N)} {Y : Finset (Fin M)} {j : ℕ} {y : Fin M}
    (h : phi2 n C lw j y) (hy : y ∈ Y) : Tr P Y (n + j) := by
  obtain ⟨hj, h1, h2⟩ := h
  exact tr_and hS hj false (tr_l hS hy h1) (tr_l hS hy h2)

def QU {N M : ℕ} (K : Finset (ℕ × Bool)) (PA : ℕ × Bool → Fin N → Prop)
    (PB : ℕ × Bool → Fin M → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, ChU (PA key) (PB key) e.1 e.2

theorem bd_QU {N M : ℕ} (K : Finset (ℕ × Bool)) (PA : ℕ × Bool → Fin N → Prop)
    (PB : ℕ × Bool → Fin M → Prop) : Bd (QU K PA PB) K.card := by
  have h := Bd_charge K (fun key (e : Fin N × Fin M) => ChU (PA key) (PB key) e.1 e.2) 1
    (fun key _ => Bd_U _ _)
  rw [one_mul] at h
  exact h

def QM {N M : ℕ} (I : Fin N → Fin M → Prop) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin M → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, ChM I (L0 key) (L1 key) e.1 e.2

theorem bd_QM {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : No4 I) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin M → Prop) : Bd (QM I K L0 L1) K.card := by
  have h := Bd_charge K (fun key (e : Fin N × Fin M) => ChM I (L0 key) (L1 key) e.1 e.2) 1
    (fun key _ => Bd_M Prod.fst Prod.snd (fun e e' h1 h2 => Prod.ext h1 h2) I h4 _ _)
  rw [one_mul] at h
  exact h

def QMP {N M : ℕ} (I : Fin N → Fin M → Prop) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin N → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ K, ChM (fun (l : Fin M) (p : Fin N) => I p l) (L0 key) (L1 key) e.2 e.1

theorem bd_QMP {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : No4 I) (K : Finset (ℕ × Bool))
    (L0 L1 : ℕ × Bool → Fin N → Prop) : Bd (QMP I K L0 L1) K.card := by
  have h := Bd_charge K (fun key (e : Fin N × Fin M) =>
      ChM (fun (l : Fin M) (p : Fin N) => I p l) (L0 key) (L1 key) e.2 e.1) 1
    (fun key _ => Bd_M Prod.snd Prod.fst (fun e e' h1 h2 => Prod.ext h2 h1) _ (No4_swap h4) _ _)
  rw [one_mul] at h
  exact h

def QF (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KO C, ChF3 n C lw I key e.1 e.2

theorem bd_QF (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) {I : Fin N → Fin M → Prop}
    (h4 : No4 I) : Bd (QF n C lw I) (4 * (KO C).card) :=
  Bd_charge (KO C) (fun key (e : Fin N × Fin M) => ChF3 n C lw I key e.1 e.2) 4
    (fun key _ => F3_fiber Prod.fst Prod.snd (fun e e' h1 h2 => Prod.ext h1 h2) lw I h4 key)

def QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KO C, ChF3 n C pw (fun (l : Fin M) (p : Fin N) => I p l) key e.2 e.1

theorem bd_QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) {I : Fin N → Fin M → Prop}
    (h4 : No4 I) : Bd (QFP n C pw I) (4 * (KO C).card) :=
  Bd_charge (KO C) (fun key (e : Fin N × Fin M) =>
      ChF3 n C pw (fun (l : Fin M) (p : Fin N) => I p l) key e.2 e.1) 4
    (fun key _ => F3_fiber Prod.snd Prod.fst (fun e e' h1 h2 => Prod.ext h2 h1) pw _
      (No4_swap h4) key)

theorem fm_line {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {N M : ℕ}
    {I : Fin N → Fin M → Prop} (φ : ℕ → Fin M → Prop) (p : Fin N) (l : Fin M) (j0 w : ℕ)
    (hR : Rr n C (n + j0) w) (h0 : φ j0 l) (hrig : ∀ y, Lb n C φ w y → I p y) :
    (∀ y, Lb n C φ w y → y = l) ∨ (∃ y, Lb n C φ (n + j0) y ∧ y ≠ l) ∨
    QM I (KO C) (fun key y => Lb n C φ (inp C key.1 key.2) y)
      (fun key y => Lb n C φ (n + key.1) y) (p, l) := by
  rcases FM3 hC φ (n + j0) w hR l with h | h | ⟨jo, b, hjo, h3, h4, h5, y, hy, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨(jo, b), mem_KO.mpr hjo, Lb_mono h4 (Lb_self h0), h5,
      Lb_mono (Rr_trans h4 (Rr_inp hC jo hjo b)) (Lb_self h0), ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (Lb_mono h3 hy')⟩)

theorem fm_pt {n : ℕ} {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C) {N M : ℕ}
    {I : Fin N → Fin M → Prop} (ψ : ℕ → Fin N → Prop) (p : Fin N) (l : Fin M) (j0 w : ℕ)
    (hR : Rr n C (n + j0) w) (h0 : ψ j0 p) (hrig : ∀ x, Lb n C ψ w x → I x l) :
    (∀ x, Lb n C ψ w x → x = p) ∨ (∃ x, Lb n C ψ (n + j0) x ∧ x ≠ p) ∨
    QMP I (KO C) (fun key x => Lb n C ψ (inp C key.1 key.2) x)
      (fun key x => Lb n C ψ (n + key.1) x) (p, l) := by
  rcases FM3 hC ψ (n + j0) w hR p with h | h | ⟨jo, b, hjo, h3, h4, h5, y, hy, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨(jo, b), mem_KO.mpr hjo, Lb_mono h4 (Lb_self h0), h5,
      Lb_mono (Rr_trans h4 (Rr_inp hC jo hjo b)) (Lb_self h0), ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (Lb_mono h3 hy')⟩)

-- fragment f06_cover
def Acc (C : Circuit) {N M : ℕ} (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (m : ℕ) : Prop :=
  ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), p ∈ P → Tr P Y m → Tr P Y C.output

def DT (n : ℕ) {N M : ℕ} (I : Fin N → Fin M → Prop)
    (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (j : ℕ) (y : Fin M) : Prop :=
  ∀ p' : Fin N, ¬ I p' y → ∃ P : Finset (Fin N), P.card ≤ 1 ∧ (∀ x ∈ P, ¬ I x y) ∧
    Tr (insert p' P) {y} (n + j)

def D0 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ j b, AndG C j ∧ PPr n C pw (inp C j b) p ∧ PPr n C lw (inp C j (!b)) l

def C15 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ rd b β, AndG C rd ∧ PPr n C pw (inp C rd b) p ∧ Acc C Tr p (inp C rd (!b)) ∧ AndG C β ∧
    Rr n C (n + β) (inp C rd (!b)) ∧ (∃ c, PPr n C lw (inp C β c) l) ∧ DT n I Tr β l

def C14 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ jr b j c j' c', AndG C jr ∧ Rr n C (n + jr) C.output ∧ PPr n C pw (inp C jr b) p ∧
    AndG C j ∧ Rr n C (n + j) (inp C jr (!b)) ∧ Rr n C (pw p) (inp C j c) ∧
    (∃ q, Rr n C (pw q) (inp C j c) ∧ ¬ I q l) ∧ AndG C j' ∧ Rr n C (n + j') (inp C j (!c)) ∧
    PPr n C lw (inp C j' c') l ∧ Rr n C (lw l) (inp C j' (!c'))

def C1 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (p : Fin N)
    (l : Fin M) : Prop :=
  ∃ g bg α bα β bβ, AndG C g ∧ Rr n C (n + g) C.output ∧ AndG C α ∧
    Rr n C (n + α) (inp C g bg) ∧ PPr n C pw (inp C α bα) p ∧ Rr n C (pw p) (inp C α (!bα)) ∧
    AndG C β ∧ Rr n C (n + β) (inp C g (!bg)) ∧ PPr n C lw (inp C β bβ) l ∧
    Rr n C (lw l) (inp C β (!bβ))

def C2h (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ g bg α bα β bβ, AndG C g ∧ Rr n C (n + g) C.output ∧ AndG C α ∧
    Rr n C (n + α) (inp C g bg) ∧ PPr n C pw (inp C α bα) p ∧ Rr n C (lw l) (inp C α (!bα)) ∧
    (∃ y, Rr n C (lw y) (inp C α (!bα)) ∧ ¬ I p y) ∧
    AndG C β ∧ Rr n C (n + β) (inp C g (!bg)) ∧ PPr n C lw (inp C β bβ) l ∧
    Rr n C (pw p) (inp C β (!bβ)) ∧ (∃ q, Rr n C (pw q) (inp C β (!bβ)) ∧ ¬ I q l)

def C4a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ ρ bρ β bβ α bα, AndG C ρ ∧ Rr n C (n + ρ) C.output ∧ Rr n C (pw p) (inp C ρ bρ) ∧
    AndG C β ∧ Rr n C (n + β) (inp C ρ (!bρ)) ∧ PPr n C lw (inp C β bβ) l ∧
    AndG C α ∧ Rr n C (n + α) (inp C β (!bβ)) ∧ PPr n C pw (inp C α bα) p ∧
    Rr n C (lw l) (inp C α (!bα)) ∧ ∃ y, Rr n C (lw y) (inp C α (!bα)) ∧ ¬ I p y

def C4b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ ρ bρ s bs β bβ, AndG C ρ ∧ Rr n C (n + ρ) C.output ∧ PPr n C pw (inp C ρ bρ) p ∧
    AndG C s ∧ Rr n C (n + s) (inp C ρ (!bρ)) ∧ Rr n C (lw l) (inp C s bs) ∧
    AndG C β ∧ Rr n C (n + β) (inp C s (!bs)) ∧ PPr n C lw (inp C β bβ) l ∧
    Rr n C (pw p) (inp C β (!bβ)) ∧ ∃ q, Rr n C (pw q) (inp C β (!bβ)) ∧ ¬ I q l

def HalfC (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (p : Fin N)
    (l : Fin M) : Prop :=
  D0 n C pw lw p l ∨ C15 n C pw lw I Tr p l ∨ C14 n C pw lw I p l ∨ C1 n C pw lw p l ∨
    C2h n C pw lw I p l ∨ C4a n C pw lw I p l ∨ C4b n C pw lw I p l

theorem cov_A {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : Sh2 n C (GPf n C pw I p l) (GLf n C lw I p l)) : D0 n C pw lw p l := by
  obtain ⟨jr, b, hjr, hout, ⟨hx, hxk⟩, ⟨hy, hyk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C jr b) →
      Tr P Y (inp C jr (!b)) → Tr P Y C.output :=
    fun P Y h1 h2 => tr_R hS hout (tr_and hS hjr b h1 h2)
  have px : ∀ x', Rr n C (pw x') (inp C jr b) → x' = p := by
    rcases hxk with h | ⟨q, hq, hnq⟩
    · exact h
    · exfalso
      exact hnq (snd11 hS (htrue {q} {l} (tr_p hS (by simp) hq) (tr_l hS (by simp) hy)))
  have py : ∀ y', Rr n C (lw y') (inp C jr (!b)) → y' = l := by
    rcases hyk with h | ⟨y', hy', hn⟩
    · exact h
    · exfalso
      exact hn (snd11 hS (htrue {p} {y'} (tr_p hS (by simp) hx) (tr_l hS (by simp) hy')))
  exact ⟨jr, b, hjr, ⟨hx, px⟩, ⟨hy, py⟩⟩

theorem cov_B1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : Sh3 n C (GPf n C pw I p l) (GPf n C pw I p l) (GLf n C lw I p l)) :
    D0 n C pw lw p l ∨ C15 n C pw lw I Tr p l := by
  obtain ⟨jr, b, j, c, hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, ⟨hb, hbk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C jr b) →
      Tr P Y (inp C j c) → Tr P Y (inp C j (!c)) → Tr P Y C.output :=
    fun P Y h1 h2 h3 => tr_R hS hout (tr_and hS hjr b h1 (tr_R hS hRj (tr_and hS hj c h2 h3)))
  have hbu : ∀ y', Rr n C (lw y') (inp C j (!c)) → y' = l := by
    rcases hbk with h | ⟨y', hy', hn⟩
    · exact h
    · exfalso
      exact hn (snd11 hS (htrue {p} {y'} (tr_p hS (by simp) hx) (tr_p hS (by simp) ha)
        (tr_l hS (by simp) hy')))
  rcases hak with hau | ⟨q, hq, hnq⟩
  · exact Or.inl ⟨j, c, hj, ⟨ha, hau⟩, ⟨hb, hbu⟩⟩
  · have hxu : ∀ x', Rr n C (pw x') (inp C jr b) → x' = p := by
      rcases hxk with h | ⟨q', hq', hnq'⟩
      · exact h
      · exfalso
        rcases snd21 hS (htrue {q', q} {l} (tr_p hS (by simp) hq') (tr_p hS (by simp) hq)
          (tr_l hS (by simp) hb)) with h | h
        · exact hnq' h
        · exact hnq h
    refine Or.inr ⟨jr, b, j, hjr, ⟨hx, hxu⟩, ?_, hj, hRj, ⟨!c, hb, hbu⟩, ?_⟩
    · intro P Y hp hm
      exact tr_R hS hout (tr_and hS hjr b (tr_p hS hp hx) hm)
    · intro p' _
      refine ⟨{q}, by simp, ?_, tr_and hS hj c (tr_p hS (by simp) hq) (tr_l hS (by simp) hb)⟩
      intro x hx'
      rw [Finset.mem_singleton.mp hx']
      exact hnq

theorem cov_B2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : Sh3 n C (GPf n C pw I p l) (GLf n C lw I p l) (GLf n C lw I p l)) :
    C15 n C pw lw I Tr p l := by
  obtain ⟨jr, b, j, c, hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, ⟨hb, hbk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C jr b) →
      Tr P Y (inp C j c) → Tr P Y (inp C j (!c)) → Tr P Y C.output :=
    fun P Y h1 h2 h3 => tr_R hS hout (tr_and hS hjr b h1 (tr_R hS hRj (tr_and hS hj c h2 h3)))
  have hxu : ∀ x', Rr n C (pw x') (inp C jr b) → x' = p := by
    rcases hxk with h | ⟨q, hq, hnq⟩
    · exact h
    · exfalso
      exact hnq (snd11 hS (htrue {q} {l} (tr_p hS (by simp) hq) (tr_l hS (by simp) ha)
        (tr_l hS (by simp) hb)))
  have hacc : Acc C Tr p (inp C jr (!b)) := by
    intro P Y hp hm
    exact tr_R hS hout (tr_and hS hjr b (tr_p hS hp hx) hm)
  have hdt : DT n I Tr j l := by
    intro p' _
    exact ⟨∅, by simp, by simp, tr_and hS hj c (tr_l hS (by simp) ha) (tr_l hS (by simp) hb)⟩
  rcases hak with hau | ⟨y1, h1, n1⟩
  · exact ⟨jr, b, j, hjr, ⟨hx, hxu⟩, hacc, hj, hRj, ⟨c, ha, hau⟩, hdt⟩
  · rcases hbk with hbu | ⟨y2, h2, n2⟩
    · exact ⟨jr, b, j, hjr, ⟨hx, hxu⟩, hacc, hj, hRj, ⟨!c, hb, hbu⟩, hdt⟩
    · exfalso
      rcases snd12 hS (htrue {p} {y1, y2} (tr_p hS (by simp) hx) (tr_l hS (by simp) h1)
        (tr_l hS (by simp) h2)) with h | h
      · exact n1 h
      · exact n2 h

theorem cov_C1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : ShBal n C (GPf n C pw I p l) (GPf n C pw I p l) (GLf n C lw I p l) (GLf n C lw I p l)) :
    C1 n C pw lw p l := by
  obtain ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hR1, ⟨ha, hak⟩, ⟨hb, hbk⟩, hj2, hR2,
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C j1 c1) →
      Tr P Y (inp C j1 (!c1)) → Tr P Y (inp C j2 c2) → Tr P Y (inp C j2 (!c2)) →
      Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => tr_R hS hout (tr_and hS hjr b (tr_R hS hR1 (tr_and hS hj1 c1 h1 h2))
      (tr_R hS hR2 (tr_and hS hj2 c2 h3 h4)))
  have hP : ∃ e, PPr n C pw (inp C j1 e) p ∧ Rr n C (pw p) (inp C j1 (!e)) := by
    rcases hak with hau | ⟨q1, hq1, n1⟩
    · exact ⟨c1, ⟨ha, hau⟩, hb⟩
    · rcases hbk with hbu | ⟨q2, hq2, n2⟩
      · exact ⟨!c1, ⟨hb, hbu⟩, by rw [Bool.not_not]; exact ha⟩
      · exfalso
        rcases snd21 hS (htrue {q1, q2} {l} (tr_p hS (by simp) hq1) (tr_p hS (by simp) hq2)
          (tr_l hS (by simp) hc) (tr_l hS (by simp) hd)) with h | h
        · exact n1 h
        · exact n2 h
  have hL : ∃ e, PPr n C lw (inp C j2 e) l ∧ Rr n C (lw l) (inp C j2 (!e)) := by
    rcases hck with hcu | ⟨y1, hy1, n1⟩
    · exact ⟨c2, ⟨hc, hcu⟩, hd⟩
    · rcases hdk with hdu | ⟨y2, hy2, n2⟩
      · exact ⟨!c2, ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc⟩
      · exfalso
        rcases snd12 hS (htrue {p} {y1, y2} (tr_p hS (by simp) ha) (tr_p hS (by simp) hb)
          (tr_l hS (by simp) hy1) (tr_l hS (by simp) hy2)) with h | h
        · exact n1 h
        · exact n2 h
  obtain ⟨e1, hp1, hp2⟩ := hP
  obtain ⟨e2, hl1, hl2⟩ := hL
  exact ⟨jr, b, j1, e1, j2, e2, hjr, hout, hj1, hR1, hp1, hp2, hj2, hR2, hl1, hl2⟩

theorem cov_C2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : ShBal n C (GPf n C pw I p l) (GLf n C lw I p l) (GPf n C pw I p l) (GLf n C lw I p l)) :
    D0 n C pw lw p l ∨ C2h n C pw lw I p l := by
  obtain ⟨jr, b, j1, c1, j2, c2, hjr, hout, hj1, hR1, ⟨ha, hak⟩, ⟨hb, hbk⟩, hj2, hR2,
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C j1 c1) →
      Tr P Y (inp C j1 (!c1)) → Tr P Y (inp C j2 c2) → Tr P Y (inp C j2 (!c2)) →
      Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => tr_R hS hout (tr_and hS hjr b (tr_R hS hR1 (tr_and hS hj1 c1 h1 h2))
      (tr_R hS hR2 (tr_and hS hj2 c2 h3 h4)))
  rcases hak with hau | ⟨qa, hqa, nqa⟩
  · rcases hbk with hbu | ⟨yb, hyb, nyb⟩
    · exact Or.inl ⟨j1, c1, hj1, ⟨ha, hau⟩, ⟨hb, hbu⟩⟩
    · have hdu : ∀ y', Rr n C (lw y') (inp C j2 (!c2)) → y' = l := by
        rcases hdk with h | ⟨yd, hyd, nyd⟩
        · exact h
        · exfalso
          rcases snd12 hS (htrue {p} {yb, yd} (tr_p hS (by simp) ha) (tr_l hS (by simp) hyb)
            (tr_p hS (by simp) hc) (tr_l hS (by simp) hyd)) with h | h
          · exact nyb h
          · exact nyd h
      rcases hck with hcu | ⟨qc, hqc, nqc⟩
      · exact Or.inl ⟨j2, c2, hj2, ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
      · exact Or.inr ⟨jr, b, j1, c1, j2, !c2, hjr, hout, hj1, hR1, ⟨ha, hau⟩, hb,
          ⟨yb, hyb, nyb⟩, hj2, hR2, ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc,
          ⟨qc, by rw [Bool.not_not]; exact hqc, nqc⟩⟩
  · have hcu : ∀ x', Rr n C (pw x') (inp C j2 c2) → x' = p := by
      rcases hck with h | ⟨qc, hqc, nqc⟩
      · exact h
      · exfalso
        rcases snd21 hS (htrue {qa, qc} {l} (tr_p hS (by simp) hqa) (tr_l hS (by simp) hb)
          (tr_p hS (by simp) hqc) (tr_l hS (by simp) hd)) with h | h
        · exact nqa h
        · exact nqc h
    rcases hdk with hdu | ⟨yd, hyd, nyd⟩
    · exact Or.inl ⟨j2, c2, hj2, ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
    · have hbu : ∀ y', Rr n C (lw y') (inp C j1 (!c1)) → y' = l := by
        rcases hbk with h | ⟨yb, hyb, nyb⟩
        · exact h
        · exfalso
          rcases snd12 hS (htrue {p} {yb, yd} (tr_p hS (by simp) ha) (tr_l hS (by simp) hyb)
            (tr_p hS (by simp) hc) (tr_l hS (by simp) hyd)) with h | h
          · exact nyb h
          · exact nyd h
      exact Or.inr ⟨jr, !b, j2, c2, j1, !c1, hjr, hout, hj2, hR2, ⟨hc, hcu⟩, hd,
        ⟨yd, hyd, nyd⟩, hj1, by rw [Bool.not_not]; exact hR1, ⟨hb, hbu⟩,
        by rw [Bool.not_not]; exact ha, ⟨qa, by rw [Bool.not_not]; exact hqa, nqa⟩⟩

theorem cov_C3 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : ShCat n C (GPf n C pw I p l) (GPf n C pw I p l) (GLf n C lw I p l) (GLf n C lw I p l)) :
    C15 n C pw lw I Tr p l ∨ C14 n C pw lw I p l := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, hj', hRj',
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C jr b) →
      Tr P Y (inp C j c) → Tr P Y (inp C j' c') → Tr P Y (inp C j' (!c')) → Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => tr_R hS hout (tr_and hS hjr b h1 (tr_R hS hRj (tr_and hS hj c h2
      (tr_R hS hRj' (tr_and hS hj' c' h3 h4)))))
  have hL : ∃ e, PPr n C lw (inp C j' e) l ∧ Rr n C (lw l) (inp C j' (!e)) := by
    rcases hck with hcu | ⟨y1, hy1, n1⟩
    · exact ⟨c', ⟨hc, hcu⟩, hd⟩
    · rcases hdk with hdu | ⟨y2, hy2, n2⟩
      · exact ⟨!c', ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc⟩
      · exfalso
        rcases snd12 hS (htrue {p} {y1, y2} (tr_p hS (by simp) hx) (tr_p hS (by simp) ha)
          (tr_l hS (by simp) hy1) (tr_l hS (by simp) hy2)) with h | h
        · exact n1 h
        · exact n2 h
  obtain ⟨e, hl1, hl2⟩ := hL
  rcases hak with hau | ⟨q, hq, nq⟩
  · refine Or.inl ⟨j, c, j', hj, ⟨ha, hau⟩, ?_, hj', hRj', ⟨e, hl1⟩, ?_⟩
    · intro P Y hp hm
      exact tr_R hS hout (tr_and hS hjr b (tr_p hS hp hx) (tr_R hS hRj
        (tr_and hS hj c (tr_p hS hp ha) hm)))
    · intro p' _
      exact ⟨∅, by simp, by simp, tr_and hS hj' c' (tr_l hS (by simp) hc)
        (tr_l hS (by simp) hd)⟩
  · have hxu : ∀ x', Rr n C (pw x') (inp C jr b) → x' = p := by
      rcases hxk with h | ⟨q', hq', nq'⟩
      · exact h
      · exfalso
        rcases snd21 hS (htrue {q', q} {l} (tr_p hS (by simp) hq') (tr_p hS (by simp) hq)
          (tr_l hS (by simp) hc) (tr_l hS (by simp) hd)) with h | h
        · exact nq' h
        · exact nq h
    exact Or.inr ⟨jr, b, j, c, j', e, hjr, hout, ⟨hx, hxu⟩, hj, hRj, ha, ⟨q, hq, nq⟩, hj',
      hRj', hl1, hl2⟩

theorem cov_C4 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : ShCat n C (GPf n C pw I p l) (GLf n C lw I p l) (GPf n C pw I p l) (GLf n C lw I p l)) :
    D0 n C pw lw p l ∨ C15 n C pw lw I Tr p l ∨ C4a n C pw lw I p l ∨ C4b n C pw lw I p l := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hx, hxk⟩, hj, hRj, ⟨ha, hak⟩, hj', hRj',
    ⟨hc, hck⟩, ⟨hd, hdk⟩⟩ := h
  have htrue : ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), Tr P Y (inp C jr b) →
      Tr P Y (inp C j c) → Tr P Y (inp C j' c') → Tr P Y (inp C j' (!c')) → Tr P Y C.output :=
    fun P Y h1 h2 h3 h4 => tr_R hS hout (tr_and hS hjr b h1 (tr_R hS hRj (tr_and hS hj c h2
      (tr_R hS hRj' (tr_and hS hj' c' h3 h4)))))
  rcases hck with hcu | ⟨qc, hqc, nqc⟩
  · rcases hdk with hdu | ⟨yd, hyd, nyd⟩
    · exact Or.inl ⟨j', c', hj', ⟨hc, hcu⟩, ⟨hd, hdu⟩⟩
    · have hau : ∀ y', Rr n C (lw y') (inp C j c) → y' = l := by
        rcases hak with h | ⟨ya, hya, nya⟩
        · exact h
        · exfalso
          rcases snd12 hS (htrue {p} {ya, yd} (tr_p hS (by simp) hx) (tr_l hS (by simp) hya)
            (tr_p hS (by simp) hc) (tr_l hS (by simp) hyd)) with h | h
          · exact nya h
          · exact nyd h
      exact Or.inr (Or.inr (Or.inl ⟨jr, b, j, c, j', c', hjr, hout, hx, hj, hRj, ⟨ha, hau⟩,
        hj', hRj', ⟨hc, hcu⟩, hd, yd, hyd, nyd⟩))
  · have hxu : ∀ x', Rr n C (pw x') (inp C jr b) → x' = p := by
      rcases hxk with h | ⟨qx, hqx, nqx⟩
      · exact h
      · exfalso
        rcases snd21 hS (htrue {qx, qc} {l} (tr_p hS (by simp) hqx) (tr_l hS (by simp) ha)
          (tr_p hS (by simp) hqc) (tr_l hS (by simp) hd)) with h | h
        · exact nqx h
        · exact nqc h
    rcases hak with hau | ⟨ya, hya, nya⟩
    · refine Or.inr (Or.inl ⟨jr, b, j, hjr, ⟨hx, hxu⟩, ?_, hj, hRj, ⟨c, ha, hau⟩, ?_⟩)
      · intro P Y hp hm
        exact tr_R hS hout (tr_and hS hjr b (tr_p hS hp hx) hm)
      · intro p' _
        refine ⟨{qc}, by simp, ?_, tr_and hS hj c (tr_l hS (by simp) ha)
          (tr_R hS hRj' (tr_and hS hj' c' (tr_p hS (by simp) hqc) (tr_l hS (by simp) hd)))⟩
        intro x hx'
        rw [Finset.mem_singleton.mp hx']
        exact nqc
    · have hdu : ∀ y', Rr n C (lw y') (inp C j' (!c')) → y' = l := by
        rcases hdk with h | ⟨yd, hyd, nyd⟩
        · exact h
        · exfalso
          rcases snd12 hS (htrue {p} {ya, yd} (tr_p hS (by simp) hx) (tr_l hS (by simp) hya)
            (tr_p hS (by simp) hc) (tr_l hS (by simp) hyd)) with h | h
          · exact nya h
          · exact nyd h
      exact Or.inr (Or.inr (Or.inr ⟨jr, b, j, c, j', !c', hjr, hout, ⟨hx, hxu⟩, hj, hRj, ha,
        hj', hRj', ⟨hd, hdu⟩, by rw [Bool.not_not]; exact hc,
        ⟨qc, by rw [Bool.not_not]; exact hqc, nqc⟩⟩))

theorem cover_prim {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M)
    (h : Prim n C (GPf n C pw I p l) (GLf n C lw I p l)) : HalfC n C pw lw I Tr p l := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (cov_A hS p l h)
  · rcases cov_B1 hS p l h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inl (cov_B2 hS p l h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (cov_C1 hS p l h))))
  · rcases cov_C2 hS p l h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
  · rcases cov_C3 hS p l h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · rcases cov_C4 hS p l h with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h')))))

-- fragment f07_special
def phi15 (n : ℕ) (C : Circuit) {N M : ℕ} (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (j : ℕ) (y : Fin M) : Prop :=
  AndG C j ∧ (∃ c, Rr n C (lw y) (inp C j c)) ∧ DT n I Tr j y

def phi14 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  AndG C j ∧ ∃ c, (∃ z, Rr n C (pw z) (inp C j c) ∧ ¬ I z y) ∧
    Lb n C (phi2 n C lw) (inp C j (!c)) y

def phi1 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (y : Fin M) : Prop :=
  AndG C j ∧ ∃ c, Rr n C (lw y) (inp C j c) ∧ Lb n C (phiB n C pw lw I) (inp C j (!c)) y

def phiNP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (j : ℕ) (yt : Fin M × Fin M) : Prop :=
  AndG C j ∧ ∃ c, Rr n C (lw yt.1) (inp C j c) ∧
    ∃ x, Lb n C (fun j' x' => Junk n C pw lw I j' x' yt.2) (inp C j (!c)) x ∧ ¬ I x yt.1

theorem pts_le_two {N M : ℕ} {I : Fin N → Fin M → Prop} (h4 : No4 I) {X : Type} (T : Finset X)
    (f : X → Fin N) (hinj : ∀ e ∈ T, ∀ e' ∈ T, f e = f e' → e = e') (l y t : Fin M)
    (hy : y ≠ l) (ht : t ≠ l) (h : ∀ e ∈ T, I (f e) l ∧ (I (f e) y ∨ I (f e) t)) :
    T.card ≤ 2 := by
  classical
  refine card_le_two_of_bool T (fun e => decide (I (f e) y)) ?_
  intro e he e' he' hdec
  have hiff : I (f e) y ↔ I (f e') y := decide_eq_decide.mp hdec
  apply hinj e he e' he'
  by_contra hne
  obtain ⟨hI, ho⟩ := h e he
  obtain ⟨hI', ho'⟩ := h e' he'
  by_cases h1 : I (f e) y
  · exact h4 (f e) (f e') l y hne (Ne.symm hy) ⟨hI, hI', h1, hiff.mp h1⟩
  · have h1' : ¬ I (f e') y := fun hh => h1 (hiff.mpr hh)
    exact h4 (f e) (f e') l t hne (Ne.symm ht)
      ⟨hI, hI', ho.resolve_left h1, ho'.resolve_left h1'⟩

theorem lines_le_two {M : ℕ} (T : Finset (Fin M)) (yt0 : Fin M × Fin M)
    (h : ∀ y ∈ T, yt0.1 = y ∨ yt0.2 = y) : T.card ≤ 2 := by
  classical
  refine card_le_two_of_bool T (fun y => decide (yt0.1 = y)) ?_
  intro y hy y' hy' hdec
  have hiff : yt0.1 = y ↔ yt0.1 = y' := decide_eq_decide.mp hdec
  by_cases h1 : yt0.1 = y
  · exact h1.symm.trans (hiff.mp h1)
  · have h1' : ¬ yt0.1 = y' := fun hh => h1 (hiff.mpr hh)
    exact ((h y hy).resolve_left h1).symm.trans ((h y' hy').resolve_left h1')

def SmallL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  PPr n C pw (inp C key.1 key.2) p ∧ Rr n C (lw l) (inp C key.1 (!key.2)) ∧ I p l ∧
    {t : Fin M | Rr n C (lw t) (inp C key.1 (!key.2)) ∧ I p t}.ncard ≤ 2

theorem fib_SL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => SmallL n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.1 = e0.1 := fun e he => hu0 _ (hS e he).1.1
    refine card_le_of_maps S Prod.snd (fun e he e' he' h =>
      Prod.ext ((hp e he).trans (hp e' he').symm) h) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, h2, h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2, h3⟩

def SmallP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  PPr n C lw (inp C key.1 key.2) l ∧ Rr n C (pw p) (inp C key.1 (!key.2)) ∧ I p l ∧
    {z : Fin N | Rr n C (pw z) (inp C key.1 (!key.2)) ∧ I z l}.ncard ≤ 2

theorem fib_SP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => SmallP n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.2 = e0.2 := fun e he => hu0 _ (hS e he).1.1
    refine card_le_of_maps S Prod.fst (fun e he e' he' h =>
      Prod.ext h ((hp e he).trans (hp e' he').symm)) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, h2, h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2, h3⟩

def SbCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  (∃ y1 y2, y1 ≠ y2 ∧ Lb n C (phi1 n C pw lw I) (n + key.1) y1 ∧
    Lb n C (phi1 n C pw lw I) (n + key.1) y2) ∧
  (∀ y, Lb n C (phi1 n C pw lw I) (n + key.1) y → I p y) ∧
  Rr n C (lw l) (inp C key.1 key.2) ∧ I p l ∧
  {t : Fin M | Rr n C (lw t) (inp C key.1 key.2) ∧ I p t}.ncard ≤ 2

theorem fib_Sb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : No4 I) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => SbCh n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨y1, y2, hne, h1, h2⟩, ha0, _, _, hk0⟩ := hS e0 he0
    have hp : ∀ e ∈ S, e.1 = e0.1 := by
      intro e he
      by_contra hne2
      have ha := (hS e he).2.1
      exact h4 e.1 e0.1 y1 y2 hne2 hne ⟨ha _ h1, ha0 _ h1, ha _ h2, ha0 _ h2⟩
    refine card_le_of_maps S Prod.snd (fun e he e' he' h =>
      Prod.ext ((hp e he).trans (hp e' he').symm) h) _ (Set.toFinite _) 2 hk0 ?_
    intro e he
    obtain ⟨_, _, h2', h3, _⟩ := hS e he
    rw [hp e he] at h3
    exact ⟨h2', h3⟩

def NbCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  PPr n C lw (inp C key.1 key.2) l ∧ I p l ∧
  (∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + key.1) yt ∧ yt.1 ≠ l ∧ yt.2 ≠ l) ∧
  ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + key.1) yt → I p yt.1 ∨ I p yt.2

theorem fib_Nb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : No4 I) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => NbCh n C pw lw I key e.1 e.2) 2 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨⟨_, hu0⟩, _, ⟨yt, hyt, hn1, hn2⟩, _⟩ := hS e0 he0
    have hl : ∀ e ∈ S, e.2 = e0.2 := fun e he => hu0 _ (hS e he).1.1
    refine pts_le_two h4 S Prod.fst (fun e he e' he' h =>
      Prod.ext h ((hl e he).trans (hl e' he').symm)) e0.2 yt.1 yt.2 hn1 hn2 ?_
    intro e he
    obtain ⟨_, hI, _, ho⟩ := hS e he
    rw [hl e he] at hI
    exact ⟨hI, ho yt hyt⟩

def NcCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  I p l ∧
  (∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C key.1 key.2) yt →
    yt.1 = l ∨ yt.2 = l) ∧
  (∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C key.1 key.2) yt) ∧
  (∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + key.1) yt ∧ yt.1 ≠ l ∧ yt.2 ≠ l) ∧
  ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + key.1) yt → I p yt.1 ∨ I p yt.2

theorem fib_Nc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    {I : Fin N → Fin M → Prop} (h4 : No4 I) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => NcCh n C pw lw I key e.1 e.2) 4 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨_, _, ⟨yt0, hyt0⟩, _, _⟩ := hS e0 he0
    have hh : S.card ≤ 2 * 2 := by
      refine card_le_prod S Prod.snd 2 2 ?_ ?_
      · intro T hT
        refine lines_le_two T yt0 ?_
        intro y hy
        obtain ⟨e, he, hey⟩ := hT y hy
        rw [← hey]
        exact (hS e he).2.1 yt0 hyt0
      · intro y T hT
        rcases T.eq_empty_or_nonempty with h | ⟨e1, he1⟩
        · simp [h]
        · obtain ⟨he1S, hy1⟩ := hT e1 he1
          obtain ⟨_, _, _, ⟨yt, hyt, hn1, hn2⟩, _⟩ := hS e1 he1S
          rw [hy1] at hn1 hn2
          refine pts_le_two h4 T Prod.fst (fun e he e' he' h =>
            Prod.ext h ((hT e he).2.trans (hT e' he').2.symm)) y yt.1 yt.2 hn1 hn2 ?_
          intro e he
          obtain ⟨heS, hye⟩ := hT e he
          obtain ⟨hI, _, _, _, ho⟩ := hS e heS
          rw [hye] at hI
          exact ⟨hI, ho yt hyt⟩
    omega

def NaCh (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) (p : Fin N) (l : Fin M) : Prop :=
  Rr n C (pw p) (inp C key.1 key.2) ∧ I p l ∧
  (∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C key.1 (!key.2)) yt →
    yt.1 = l ∨ yt.2 = l) ∧
  (∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C key.1 (!key.2)) yt) ∧
  {z : Fin N | Rr n C (pw z) (inp C key.1 key.2) ∧ I z l}.ncard ≤ 2

theorem fib_Na (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (key : ℕ × Bool) :
    Bd (fun e : Fin N × Fin M => NaCh n C pw lw I key e.1 e.2) 4 := by
  intro S hS
  rcases S.eq_empty_or_nonempty with h | ⟨e0, he0⟩
  · simp [h]
  · obtain ⟨_, _, _, ⟨yt0, hyt0⟩, _⟩ := hS e0 he0
    have hh : S.card ≤ 2 * 2 := by
      refine card_le_prod S Prod.snd 2 2 ?_ ?_
      · intro T hT
        refine lines_le_two T yt0 ?_
        intro y hy
        obtain ⟨e, he, hey⟩ := hT y hy
        rw [← hey]
        exact (hS e he).2.2.1 yt0 hyt0
      · intro y T hT
        rcases T.eq_empty_or_nonempty with h | ⟨e1, he1⟩
        · simp [h]
        · obtain ⟨he1S, hy1⟩ := hT e1 he1
          have hk := (hS e1 he1S).2.2.2.2
          rw [hy1] at hk
          refine card_le_of_maps T Prod.fst (fun e he e' he' h =>
            Prod.ext h ((hT e he).2.trans (hT e' he').2.symm)) _ (Set.toFinite _) 2 hk ?_
          intro e he
          obtain ⟨heS, hye⟩ := hT e he
          obtain ⟨h1, hI, _⟩ := hS e heS
          rw [hye] at hI
          exact ⟨h1, hI⟩
    omega

-- fragment f08_fam
def F_D0 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key x => Rr n C (pw x) (inp C key.1 key.2)) (fun key y => Rr n C (lw y) (inp C key.1 (!key.2))) e

def F_15a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key x => Rr n C (pw x) (inp C key.1 key.2)) (fun key y => Lb n C (phi15 n C lw I Tr) (inp C key.1 (!key.2)) y) e

def F_15b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KA C) (fun key y => Rr n C (lw y) (inp C key.1 key.2)) (fun key y => Lb n C (phi15 n C lw I Tr) (n + key.1) y) e

def F_15c (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KO C) (fun key y => Lb n C (phi15 n C lw I Tr) (inp C key.1 key.2) y) (fun key y => Lb n C (phi15 n C lw I Tr) (n + key.1) y) e

def F_LL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KO C) (fun key y => Lb n C (phi2 n C lw) (inp C key.1 key.2) y) (fun key y => Lb n C (phi2 n C lw) (n + key.1) y) e

def F_14a (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key x => Rr n C (pw x) (inp C key.1 key.2)) (fun key y => Lb n C (phi14 n C pw lw I) (inp C key.1 (!key.2)) y) e

def F_14b (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KA C) (fun key y => Lb n C (phi2 n C lw) (inp C key.1 (!key.2)) y) (fun key y => Lb n C (phi14 n C pw lw I) (n + key.1) y) e

def F_14c (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KO C) (fun key y => Lb n C (phi14 n C pw lw I) (inp C key.1 key.2) y) (fun key y => Lb n C (phi14 n C pw lw I) (n + key.1) y) e

def F_C1g (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key y => Lb n C (phi2 n C pw) (inp C key.1 key.2) y) (fun key y => Lb n C (phi2 n C lw) (inp C key.1 (!key.2)) y) e

def F_PP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QMP I (KO C) (fun key y => Lb n C (phi2 n C pw) (inp C key.1 key.2) y) (fun key y => Lb n C (phi2 n C pw) (n + key.1) y) e

def F_SL (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KA C, SmallL n C pw lw I key e.1 e.2

def F_SP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KA C, SmallP n C pw lw I key e.1 e.2

def F_Sb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QMP I (KA C) (fun key x => Rr n C (pw x) (inp C key.1 key.2)) (fun key y => Lb n C (phiS n C pw lw I) (n + key.1) y) e

def F_Sc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QMP I (KO C) (fun key y => Lb n C (phiS n C pw lw I) (inp C key.1 key.2) y) (fun key y => Lb n C (phiS n C pw lw I) (n + key.1) y) e

def F_C2g (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key y => Lb n C (phiS n C pw lw I) (inp C key.1 key.2) y) (fun key y => Lb n C (phiB n C pw lw I) (inp C key.1 (!key.2)) y) e

def F_Bb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KA C) (fun key y => Rr n C (lw y) (inp C key.1 key.2)) (fun key y => Lb n C (phiB n C pw lw I) (n + key.1) y) e

def F_Bc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KO C) (fun key y => Lb n C (phiB n C pw lw I) (inp C key.1 key.2) y) (fun key y => Lb n C (phiB n C pw lw I) (n + key.1) y) e

def F_4aE (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key y => Lb n C (phiS n C pw lw I) (inp C key.1 (!key.2)) y) (fun key y => Rr n C (lw y) (inp C key.1 key.2)) e

def F_Nb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KA C, NbCh n C pw lw I key e.1 e.2

def F_Nc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KO C, NcCh n C pw lw I key e.1 e.2

def F_Na (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KA C, NaCh n C pw lw I key e.1 e.2

def F_4ba (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QU (KA C) (fun key x => Rr n C (pw x) (inp C key.1 key.2)) (fun key y => Lb n C (phi1 n C pw lw I) (inp C key.1 (!key.2)) y) e

def F_4bc (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KO C) (fun key y => Lb n C (phi1 n C pw lw I) (inp C key.1 key.2) y) (fun key y => Lb n C (phi1 n C pw lw I) (n + key.1) y) e

def F_Sbb (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  ∃ key ∈ KA C, SbCh n C pw lw I key e.1 e.2

def F_4b2 (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QM I (KA C) (fun key y => Lb n C (phiB n C pw lw I) (inp C key.1 (!key.2)) y) (fun key y => Lb n C (phi1 n C pw lw I) (n + key.1) y) e

def F_QF (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QF n C lw I e

def F_QFP (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  QFP n C pw I e

def HQ (n : ℕ) (C : Circuit) {N M : ℕ} (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop) (e : Fin N × Fin M) : Prop :=
  F_D0 n C pw lw I Tr e ∨ F_15a n C pw lw I Tr e ∨ F_15b n C pw lw I Tr e ∨ F_15c n C pw lw I Tr e ∨ F_LL n C pw lw I Tr e ∨ F_14a n C pw lw I Tr e ∨ F_14b n C pw lw I Tr e ∨ F_14c n C pw lw I Tr e ∨ F_C1g n C pw lw I Tr e ∨ F_PP n C pw lw I Tr e ∨ F_SL n C pw lw I Tr e ∨ F_SP n C pw lw I Tr e ∨ F_Sb n C pw lw I Tr e ∨ F_Sc n C pw lw I Tr e ∨ F_C2g n C pw lw I Tr e ∨ F_Bb n C pw lw I Tr e ∨ F_Bc n C pw lw I Tr e ∨ F_4aE n C pw lw I Tr e ∨ F_Nb n C pw lw I Tr e ∨ F_Nc n C pw lw I Tr e ∨ F_Na n C pw lw I Tr e ∨ F_4ba n C pw lw I Tr e ∨ F_4bc n C pw lw I Tr e ∨ F_Sbb n C pw lw I Tr e ∨ F_4b2 n C pw lw I Tr e ∨ F_QF n C pw lw I Tr e ∨ F_QFP n C pw lw I Tr e

theorem hq_D0 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_D0 n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inl h

theorem hq_15a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_15a n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inl h)

theorem hq_15b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_15b n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inl h))

theorem hq_15c {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_15c n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem hq_LL {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_LL n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem hq_14a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_14a n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem hq_14b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_14b n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem hq_14c {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_14c n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem hq_C1g {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_C1g n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

theorem hq_PP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_PP n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))

theorem hq_SL {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_SL n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))

theorem hq_SP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_SP n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))

theorem hq_Sb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Sb n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))

theorem hq_Sc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Sc n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))

theorem hq_C2g {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_C2g n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))

theorem hq_Bb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Bb n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))

theorem hq_Bc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Bc n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))

theorem hq_4aE {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_4aE n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))

theorem hq_Nb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Nb n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))

theorem hq_Nc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Nc n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))

theorem hq_Na {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Na n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))

theorem hq_4ba {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_4ba n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))

theorem hq_4bc {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_4bc n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))

theorem hq_Sbb {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_Sbb n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))

theorem hq_4b2 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_4b2 n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))

theorem hq_QF {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_QF n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))

theorem hq_QFP {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} {e : Fin N × Fin M} (h : F_QFP n C pw lw I Tr e) : HQ n C pw lw I Tr e :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))))))))))))))))))))))

theorem bd_HQ {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) :
    Bd (HQ n C pw lw I Tr) (24 * (KA C).card + 19 * (KO C).card) := by
  have h4 : No4 I := hS.2.2.2.2.2.1
  have b_D0 : Bd (F_D0 n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_15a : Bd (F_15a n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_15b : Bd (F_15b n C pw lw I Tr) ((KA C).card) := bd_QM h4 _ _ _
  have b_15c : Bd (F_15c n C pw lw I Tr) ((KO C).card) := bd_QM h4 _ _ _
  have b_LL : Bd (F_LL n C pw lw I Tr) ((KO C).card) := bd_QM h4 _ _ _
  have b_14a : Bd (F_14a n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_14b : Bd (F_14b n C pw lw I Tr) ((KA C).card) := bd_QM h4 _ _ _
  have b_14c : Bd (F_14c n C pw lw I Tr) ((KO C).card) := bd_QM h4 _ _ _
  have b_C1g : Bd (F_C1g n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_PP : Bd (F_PP n C pw lw I Tr) ((KO C).card) := bd_QMP h4 _ _ _
  have b_SL : Bd (F_SL n C pw lw I Tr) (2 * (KA C).card) := Bd_charge (KA C) _ 2 (fun key _ => fib_SL n C pw lw I key)
  have b_SP : Bd (F_SP n C pw lw I Tr) (2 * (KA C).card) := Bd_charge (KA C) _ 2 (fun key _ => fib_SP n C pw lw I key)
  have b_Sb : Bd (F_Sb n C pw lw I Tr) ((KA C).card) := bd_QMP h4 _ _ _
  have b_Sc : Bd (F_Sc n C pw lw I Tr) ((KO C).card) := bd_QMP h4 _ _ _
  have b_C2g : Bd (F_C2g n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_Bb : Bd (F_Bb n C pw lw I Tr) ((KA C).card) := bd_QM h4 _ _ _
  have b_Bc : Bd (F_Bc n C pw lw I Tr) ((KO C).card) := bd_QM h4 _ _ _
  have b_4aE : Bd (F_4aE n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_Nb : Bd (F_Nb n C pw lw I Tr) (2 * (KA C).card) := Bd_charge (KA C) _ 2 (fun key _ => fib_Nb n C pw lw h4 key)
  have b_Nc : Bd (F_Nc n C pw lw I Tr) (4 * (KO C).card) := Bd_charge (KO C) _ 4 (fun key _ => fib_Nc n C pw lw h4 key)
  have b_Na : Bd (F_Na n C pw lw I Tr) (4 * (KA C).card) := Bd_charge (KA C) _ 4 (fun key _ => fib_Na n C pw lw I key)
  have b_4ba : Bd (F_4ba n C pw lw I Tr) ((KA C).card) := bd_QU _ _ _
  have b_4bc : Bd (F_4bc n C pw lw I Tr) ((KO C).card) := bd_QM h4 _ _ _
  have b_Sbb : Bd (F_Sbb n C pw lw I Tr) (2 * (KA C).card) := Bd_charge (KA C) _ 2 (fun key _ => fib_Sb n C pw lw h4 key)
  have b_4b2 : Bd (F_4b2 n C pw lw I Tr) ((KA C).card) := bd_QM h4 _ _ _
  have b_QF : Bd (F_QF n C pw lw I Tr) (4 * (KO C).card) := bd_QF n C lw h4
  have b_QFP : Bd (F_QFP n C pw lw I Tr) (4 * (KO C).card) := bd_QFP n C pw h4
  refine Bd_le ?_ (Bd_or (b_D0) (Bd_or (b_15a) (Bd_or (b_15b) (Bd_or (b_15c) (Bd_or (b_LL) (Bd_or (b_14a) (Bd_or (b_14b) (Bd_or (b_14c) (Bd_or (b_C1g) (Bd_or (b_PP) (Bd_or (b_SL) (Bd_or (b_SP) (Bd_or (b_Sb) (Bd_or (b_Sc) (Bd_or (b_C2g) (Bd_or (b_Bb) (Bd_or (b_Bc) (Bd_or (b_4aE) (Bd_or (b_Nb) (Bd_or (b_Nc) (Bd_or (b_Na) (Bd_or (b_4ba) (Bd_or (b_4bc) (Bd_or (b_Sbb) (Bd_or (b_4b2) (Bd_or (b_QF) (b_QFP)))))))))))))))))))))))))))
  omega

-- fragment f09_classes
theorem junk_not {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {j : ℕ} {x : Fin N} {t : Fin M} (h : Junk n C pw lw I j x t) :
    ¬ I x t := by
  obtain ⟨_, _, _, _, hn⟩ := h
  exact hn

theorem phi2_of {n : ℕ} {C : Circuit} {K : ℕ} {xw : Fin K → ℕ} {j : ℕ} (hj : AndG C j) (c : Bool)
    {x : Fin K} (h1 : Rr n C (xw x) (inp C j c)) (h2 : Rr n C (xw x) (inp C j (!c))) :
    phi2 n C xw j x := by
  cases c
  · exact ⟨hj, h1, h2⟩
  · exact ⟨hj, h2, h1⟩

theorem phi2_at {n : ℕ} {C : Circuit} {K : ℕ} {xw : Fin K → ℕ} {j : ℕ} {x : Fin K}
    (h : phi2 n C xw j x) (c : Bool) : Rr n C (xw x) (inp C j c) := by
  cases c
  · exact h.2.1
  · exact h.2.2

theorem hq_of_D0 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : D0 n C pw lw p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨j, b, hj, ⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
  exact hq_D0 ⟨(j, b), mem_KA.mpr hj, h1, h2, h3, h4⟩

theorem rig15 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) {p : Fin N} {m : ℕ} {y : Fin M} (hacc : Acc C Tr p m)
    (hl : Lb n C (phi15 n C lw I Tr) m y) : I p y := by
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  by_contra hn
  obtain ⟨j, hR, _, _, hdt⟩ := hl
  obtain ⟨P, hP1, hPn, htr⟩ := hdt p hn
  have hout := hacc (insert p P) {y} (Finset.mem_insert_self p P) (htR _ _ _ _ hR htr)
  obtain ⟨x, hx, y', hy', hI'⟩ := hsnd (insert p P) {y}
    ((Finset.card_insert_le p P).trans (by omega)) (by simp) hout
  rw [Finset.mem_singleton] at hy'
  rw [hy'] at hI'
  rcases Finset.mem_insert.mp hx with h | h
  · rw [h] at hI'
    exact hn hI'
  · exact hPn x h hI'

theorem hq_of_C15 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : C15 n C pw lw I Tr p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨rd, b, β, hrd, ⟨hp1, hp2⟩, hacc, hβ, hRβ, ⟨c, hl1, hl2⟩, hdt⟩ := h
  have hC := hS.1
  have h0 : phi15 n C lw I Tr β l := ⟨hβ, ⟨c, hl1⟩, hdt⟩
  have hrig : ∀ y, Lb n C (phi15 n C lw I Tr) (inp C rd (!b)) y → I p y :=
    fun y hy => rig15 hS hacc hy
  rcases fm_line hC (phi15 n C lw I Tr) p l β (inp C rd (!b)) hRβ h0 hrig with
    h | ⟨y, hy, hne⟩ | h
  · exact hq_15a ⟨(rd, b), mem_KA.mpr hrd, hp1, hp2, Lb_mono hRβ (Lb_self h0), h⟩
  · exact hq_15b ⟨(β, c), mem_KA.mpr hβ, hl1, hl2, Lb_self h0, ⟨y, hy, hne⟩,
      fun y' hy' => hrig y' (Lb_mono hRβ hy')⟩
  · exact hq_15c h

theorem hq_of_C14 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : C14 n C pw lw I p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨jr, b, j, c, j', c', hjr, hout, ⟨hp1, hp2⟩, hj, hRj, ha, ⟨q, hq, nq⟩, hj', hRj',
    ⟨hl1, hl2⟩, hl3⟩ := h
  have hC := hS.1
  have h2 : phi2 n C lw j' l := phi2_of hj' c' hl1 hl3
  have hrig2 : ∀ y, Lb n C (phi2 n C lw) (inp C j (!c)) y → I p y := by
    intro y hy
    obtain ⟨j2, hR2, hphi⟩ := hy
    exact snd11 hS (x := p) (y := y) (tr_R hS hout (tr_and hS hjr b (tr_p hS (by simp) hp1)
      (tr_R hS hRj (tr_and hS hj c (tr_p hS (by simp) ha)
        (tr_R hS hR2 (phi2l_tr hS hphi (by simp)))))))
  rcases fm_line hC (phi2 n C lw) p l j' (inp C j (!c)) hRj' h2 hrig2 with
    ha2 | ⟨y, hy, hne⟩ | hc2
  · have h14 : phi14 n C pw lw I j l := ⟨hj, c, ⟨q, hq, nq⟩, Lb_mono hRj' (Lb_self h2)⟩
    have hrig1 : ∀ y, Lb n C (phi14 n C pw lw I) (inp C jr (!b)) y → I p y := by
      intro y hy
      obtain ⟨j1, hR1, hj1, c1, ⟨z, hz, nz⟩, ⟨j2, hR2, hphi⟩⟩ := hy
      rcases snd21 hS (x := p) (z := z) (y := y) (tr_R hS hout (tr_and hS hjr b
        (tr_p hS (by simp) hp1) (tr_R hS hR1 (tr_and hS hj1 c1 (tr_p hS (by simp) hz)
          (tr_R hS hR2 (phi2l_tr hS hphi (by simp))))))) with h | h
      · exact h
      · exact absurd h nz
    rcases fm_line hC (phi14 n C pw lw I) p l j (inp C jr (!b)) hRj h14 hrig1 with
      ha1 | ⟨y, hy, hne⟩ | hc1
    · exact hq_14a ⟨(jr, b), mem_KA.mpr hjr, hp1, hp2, Lb_mono hRj (Lb_self h14), ha1⟩
    · exact hq_14b ⟨(j, c), mem_KA.mpr hj, Lb_mono hRj' (Lb_self h2), ha2, Lb_self h14,
        ⟨y, hy, hne⟩, fun y' hy' => hrig1 y' (Lb_mono hRj hy')⟩
    · exact hq_14c hc1
  · exfalso
    exact hne (hl2 _ (phi2_at (Lb_and hC hj' hy) c'))
  · exact hq_LL hc2

theorem hq_of_C1 {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (h : C1 n C pw lw p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨g, bg, α, bα, β, bβ, hg, hout, hα, hRα, ⟨hp1, hp2⟩, hp3, hβ, hRβ, ⟨hl1, hl2⟩,
    hl3⟩ := h
  have hC := hS.1
  have hψ : phi2 n C pw α p := phi2_of hα bα hp1 hp3
  have hφ : phi2 n C lw β l := phi2_of hβ bβ hl1 hl3
  have rig : ∀ x y, Lb n C (phi2 n C pw) (inp C g bg) x →
      Lb n C (phi2 n C lw) (inp C g (!bg)) y → I x y := by
    intro x y hx hy
    obtain ⟨j1, hR1, h1⟩ := hx
    obtain ⟨j2, hR2, h2⟩ := hy
    exact snd11 hS (x := x) (y := y) (tr_R hS hout (tr_and hS hg bg
      (tr_R hS hR1 (phi2p_tr hS h1 (by simp))) (tr_R hS hR2 (phi2l_tr hS h2 (by simp)))))
  have hLp : Lb n C (phi2 n C pw) (inp C g bg) p := Lb_mono hRα (Lb_self hψ)
  have hLl : Lb n C (phi2 n C lw) (inp C g (!bg)) l := Lb_mono hRβ (Lb_self hφ)
  rcases fm_line hC (phi2 n C lw) p l β (inp C g (!bg)) hRβ hφ (fun y hy => rig p y hLp hy) with
    ha | ⟨y, hy, hne⟩ | hc
  · rcases fm_pt hC (phi2 n C pw) p l α (inp C g bg) hRα hψ (fun x hx => rig x l hx hLl) with
      ha' | ⟨x, hx, hne⟩ | hc'
    · exact hq_C1g ⟨(g, bg), mem_KA.mpr hg, hLp, ha', hLl, ha⟩
    · exfalso
      exact hne (hp2 _ (phi2_at (Lb_and hC hα hx) bα))
    · exact hq_PP hc'
  · exfalso
    exact hne (hl2 _ (phi2_at (Lb_and hC hβ hy) bβ))
  · exact hq_LL hc

theorem hq_of_C2h {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : C2h n C pw lw I p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨g, bg, α, bα, β, bβ, hg, hout, hα, hRα, ⟨hp1, hp2⟩, hla, ⟨y0, hy0, n0⟩, hβ, hRβ,
    ⟨hl1, hl2⟩, hpb, ⟨q0, hq0, nq0⟩⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hJa : ∀ t, Rr n C (lw t) (inp C α (!bα)) → ¬ I p t → Junk n C pw lw I α p t :=
    fun t ht hn => ⟨hα, bα, hp1, ht, hn⟩
  have hJb : ∀ z, Rr n C (pw z) (inp C β (!bβ)) → ¬ I z l → Junk n C pw lw I β z l :=
    fun z hz hn => ⟨hβ, !bβ, hz, by rw [Bool.not_not]; exact hl1, hn⟩
  have hψ0 : phiS n C pw lw I α p := ⟨y0, hJa y0 hy0 n0⟩
  have hφ0 : phiB n C pw lw I β l := ⟨q0, hJb q0 hq0 nq0⟩
  have JS : ∀ j1 x t j2 z y, Rr n C (n + j1) (inp C g bg) → Junk n C pw lw I j1 x t →
      Rr n C (n + j2) (inp C g (!bg)) → Junk n C pw lw I j2 z y → I x y ∨ I z t := by
    intro j1 x t j2 z y h1 J1 h2 J2
    rcases snd22 hS (x := x) (z := z) (y := t) (t := y) (tr_R hS hout (tr_and hS hg bg
      (tr_R hS h1 (junk_tr hS J1 (by simp) (by simp)))
      (tr_R hS h2 (junk_tr hS J2 (by simp) (by simp))))) with h | h | h | h
    · exact absurd h (junk_not J1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (junk_not J2)
  by_cases hY : ∃ y', Lb n C (phiB n C pw lw I) (inp C g (!bg)) y' ∧ ¬ I p y'
  · obtain ⟨y', ⟨j2, hR2, z', J2⟩, ny'⟩ := hY
    have hz : ∀ t, Rr n C (lw t) (inp C α (!bα)) → I p t ∨ I z' t := by
      intro t ht
      by_cases hpt : I p t
      · exact Or.inl hpt
      · rcases JS α p t j2 z' y' hRα (hJa t ht hpt) hR2 J2 with h | h
        · exact absurd h ny'
        · exact Or.inr h
    by_cases h3 : 3 ≤ {t : Fin M | Rr n C (lw t) (inp C α (!bα)) ∧ I p t}.ncard
    · obtain ⟨jo, b', hjo, hch⟩ := F3_exists hC lw hlw hln I (inp C α (!bα)) p l hla hI h3 z' hz
      exact hq_QF ⟨(jo, b'), mem_KO.mpr hjo, hch⟩
    · exact hq_SL ⟨(α, bα), mem_KA.mpr hα, ⟨hp1, hp2⟩, hla, hI,
        Nat.le_of_lt_succ (not_le.mp h3)⟩
  by_cases hX : ∃ x', Lb n C (phiS n C pw lw I) (inp C g bg) x' ∧ ¬ I x' l
  · obtain ⟨x', ⟨j1, hR1, t', J1⟩, nx'⟩ := hX
    have hz : ∀ z, Rr n C (pw z) (inp C β (!bβ)) → I z l ∨ I z t' := by
      intro z hzz
      by_cases hzl : I z l
      · exact Or.inl hzl
      · rcases JS j1 x' t' β z l hR1 J1 hRβ (hJb z hzz hzl) with h | h
        · exact absurd h nx'
        · exact Or.inr h
    by_cases h3 : 3 ≤ {z : Fin N | Rr n C (pw z) (inp C β (!bβ)) ∧ I z l}.ncard
    · obtain ⟨jo, b', hjo, hch⟩ := F3_exists hC pw hpw hpn
        (fun (l : Fin M) (p : Fin N) => I p l) (inp C β (!bβ)) l p hpb hI h3 t' hz
      exact hq_QFP ⟨(jo, b'), mem_KO.mpr hjo, hch⟩
    · exact hq_SP ⟨(β, bβ), mem_KA.mpr hβ, ⟨hl1, hl2⟩, hpb, hI,
        Nat.le_of_lt_succ (not_le.mp h3)⟩
  have hnX : ∀ x, Lb n C (phiS n C pw lw I) (inp C g bg) x → I x l := by
    intro x hx
    by_contra hn
    exact hX ⟨x, hx, hn⟩
  have hnY : ∀ y, Lb n C (phiB n C pw lw I) (inp C g (!bg)) y → I p y := by
    intro y hy
    by_contra hn
    exact hY ⟨y, hy, hn⟩
  have hLp : Lb n C (phiS n C pw lw I) (inp C g bg) p := Lb_mono hRα (Lb_self hψ0)
  have hLl : Lb n C (phiB n C pw lw I) (inp C g (!bg)) l := Lb_mono hRβ (Lb_self hφ0)
  rcases fm_pt hC (phiS n C pw lw I) p l α (inp C g bg) hRα hψ0 hnX with
    ha | ⟨x, hx, hne⟩ | hc
  · rcases fm_line hC (phiB n C pw lw I) p l β (inp C g (!bg)) hRβ hφ0 hnY with
      ha' | ⟨y, hy, hne⟩ | hc'
    · exact hq_C2g ⟨(g, bg), mem_KA.mpr hg, hLp, ha, hLl, ha'⟩
    · exact hq_Bb ⟨(β, bβ), mem_KA.mpr hβ, hl1, hl2, Lb_self hφ0, ⟨y, hy, hne⟩,
        fun y' hy' => hnY y' (Lb_mono hRβ hy')⟩
    · exact hq_Bc hc'
  · exact hq_Sb ⟨(α, bα), mem_KA.mpr hα, hp1, hp2, Lb_self hψ0, ⟨x, hx, hne⟩,
      fun x' hx' => hnX x' (Lb_mono hRα hx')⟩
  · exact hq_Sc hc

theorem hq_of_C4a {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : C4a n C pw lw I p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨ρ, bρ, β, bβ, α, bα, hρ, hout, hpx, hβ, hRβ, ⟨hl1, hl2⟩, hα, hRα, ⟨hp1, hp2⟩, hla,
    y0, hy0, n0⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hψ0 : phiS n C pw lw I α p := ⟨y0, hα, bα, hp1, hy0, n0⟩
  by_cases hE : ∀ x, Lb n C (phiS n C pw lw I) (inp C β (!bβ)) x → I x l
  · rcases fm_pt hC (phiS n C pw lw I) p l α (inp C β (!bβ)) hRα hψ0 hE with
      ha | ⟨x, hx, hne⟩ | hc
    · exact hq_4aE ⟨(β, bβ), mem_KA.mpr hβ, Lb_mono hRα (Lb_self hψ0), ha, hl1, hl2⟩
    · exact hq_Sb ⟨(α, bα), mem_KA.mpr hα, hp1, hp2, Lb_self hψ0, ⟨x, hx, hne⟩,
        fun x' hx' => hE x' (Lb_mono hRα hx')⟩
    · exact hq_Sc hc
  · have hN : ∃ p', Lb n C (phiS n C pw lw I) (inp C β (!bβ)) p' ∧ ¬ I p' l := by
      by_contra hh
      apply hE
      intro x hx
      by_contra hn
      exact hh ⟨x, hx, hn⟩
    obtain ⟨p', ⟨α', hR', t', J'⟩, np'⟩ := hN
    have own : phiNP n C pw lw I β (l, t') := ⟨hβ, bβ, hl1, p', ⟨α', hR', J'⟩, np'⟩
    have CP : ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C ρ (!bρ)) yt →
        ∀ x, Rr n C (pw x) (inp C ρ bρ) → I x yt.1 ∨ I x yt.2 := by
      intro yt hyt x hx
      obtain ⟨j, hRj, hj, c, hy, x'', ⟨j', hRj', J⟩, hn⟩ := hyt
      rcases snd22 hS (x := x) (z := x'') (y := yt.1) (t := yt.2) (tr_R hS hout
        (tr_and hS hρ bρ (tr_p hS (by simp) hx) (tr_R hS hRj (tr_and hS hj c
          (tr_l hS (by simp) hy) (tr_R hS hRj' (junk_tr hS J (by simp) (by simp))))))) with
        h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hn
      · exact absurd h (junk_not J)
    have hown : Lb n C (phiNP n C pw lw I) (inp C ρ (!bρ)) (l, t') := Lb_mono hRβ (Lb_self own)
    by_cases ha : ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (inp C ρ (!bρ)) yt →
        yt.1 = l ∨ yt.2 = l
    · by_cases hQ : 3 ≤ {z : Fin N | Rr n C (pw z) (inp C ρ bρ) ∧ I z l}.ncard
      · obtain ⟨jo, b', hjo, hch⟩ := F3_exists hC pw hpw hpn
          (fun (l : Fin M) (p : Fin N) => I p l) (inp C ρ bρ) l p hpx hI hQ t'
          (fun z hz => CP (l, t') hown z hz)
        exact hq_QFP ⟨(jo, b'), mem_KO.mpr hjo, hch⟩
      · exact hq_Na ⟨(ρ, bρ), mem_KA.mpr hρ, hpx, hI, ha, ⟨(l, t'), hown⟩,
          Nat.le_of_lt_succ (not_le.mp hQ)⟩
    · by_cases hb : ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + β) yt →
          yt.1 = l ∨ yt.2 = l
      · obtain ⟨jo, b', hjo, h3, h4', h5, h6⟩ := FMG hC
          (fun v => ∀ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) v yt → yt.1 = l ∨ yt.2 = l)
          (n + β) (inp C ρ (!bρ)) hRβ hb ha
        have h6' : ∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + jo) yt ∧
            yt.1 ≠ l ∧ yt.2 ≠ l := by
          by_contra hh
          apply h6
          intro yt hyt
          by_contra hn
          exact hh ⟨yt, hyt, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
        exact hq_Nc ⟨(jo, b'), mem_KO.mpr hjo, hI, h5, ⟨(l, t'), Lb_mono h4' (Lb_self own)⟩,
          h6', fun yt hyt => CP yt (Lb_mono h3 hyt) p hpx⟩
      · have hb' : ∃ yt : Fin M × Fin M, Lb n C (phiNP n C pw lw I) (n + β) yt ∧
            yt.1 ≠ l ∧ yt.2 ≠ l := by
          by_contra hh
          apply hb
          intro yt hyt
          by_contra hn
          exact hh ⟨yt, hyt, fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
        exact hq_Nb ⟨(β, bβ), mem_KA.mpr hβ, ⟨hl1, hl2⟩, hI, hb',
          fun yt hyt => CP yt (Lb_mono hRβ hyt) p hpx⟩

theorem hq_of_C4b {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l) (h : C4b n C pw lw I p l) :
    HQ n C pw lw I Tr (p, l) := by
  obtain ⟨ρ, bρ, s, bs, β, bβ, hρ, hout, ⟨hp1, hp2⟩, hs, hRs, hls, hβ, hRβ, ⟨hl1, hl2⟩, hpb,
    q0, hq0, nq0⟩ := h
  obtain ⟨hC, hpw, hlw, hpn, hln, h4, htp, htl, htR, htA, hsnd⟩ := id hS
  have hB0 : phiB n C pw lw I β l :=
    ⟨q0, hβ, !bβ, hq0, by rw [Bool.not_not]; exact hl1, nq0⟩
  have h10 : phi1 n C pw lw I s l := ⟨hs, bs, hls, Lb_mono hRβ (Lb_self hB0)⟩
  have R1 : ∀ y, Lb n C (phi1 n C pw lw I) (inp C ρ (!bρ)) y → I p y := by
    intro y hy
    obtain ⟨j, hRj, hj, c, hyc, j', hRj', z, J⟩ := hy
    rcases snd21 hS (x := p) (z := z) (y := y) (tr_R hS hout (tr_and hS hρ bρ
      (tr_p hS (by simp) hp1) (tr_R hS hRj (tr_and hS hj c (tr_l hS (by simp) hyc)
        (tr_R hS hRj' (junk_tr hS J (by simp) (by simp))))))) with h | h
    · exact h
    · exact absurd h (junk_not J)
  rcases fm_line hC (phi1 n C pw lw I) p l s (inp C ρ (!bρ)) hRs h10 R1 with
    ha | ⟨y2, hy2, hne2⟩ | hc
  · exact hq_4ba ⟨(ρ, bρ), mem_KA.mpr hρ, hp1, hp2, Lb_mono hRs (Lb_self h10), ha⟩
  · have Hs1 : ∀ y, Lb n C (phi1 n C pw lw I) (n + s) y → I p y :=
      fun y hy => R1 y (Lb_mono hRs hy)
    by_cases hY : ∃ y'', Lb n C (phiB n C pw lw I) (inp C s (!bs)) y'' ∧ ¬ I p y''
    · obtain ⟨y'', ⟨j'', hR'', z'', J''⟩, ny''⟩ := hY
      have hz : ∀ t, Rr n C (lw t) (inp C s bs) → I p t ∨ I z'' t := by
        intro t ht
        rcases snd22 hS (x := p) (z := z'') (y := t) (t := y'') (tr_R hS hout
          (tr_and hS hρ bρ (tr_p hS (by simp) hp1) (tr_R hS hRs (tr_and hS hs bs
            (tr_l hS (by simp) ht) (tr_R hS hR'' (junk_tr hS J'' (by simp) (by simp))))))) with
          h | h | h | h
        · exact Or.inl h
        · exact absurd h ny''
        · exact Or.inr h
        · exact absurd h (junk_not J'')
      by_cases h3 : 3 ≤ {t : Fin M | Rr n C (lw t) (inp C s bs) ∧ I p t}.ncard
      · obtain ⟨jo, b', hjo, hch⟩ := F3_exists hC lw hlw hln I (inp C s bs) p l hls hI h3 z'' hz
        exact hq_QF ⟨(jo, b'), mem_KO.mpr hjo, hch⟩
      · exact hq_Sbb ⟨(s, bs), mem_KA.mpr hs, ⟨y2, l, hne2, hy2, Lb_self h10⟩, Hs1, hls, hI,
          Nat.le_of_lt_succ (not_le.mp h3)⟩
    · have hnY : ∀ y, Lb n C (phiB n C pw lw I) (inp C s (!bs)) y → I p y := by
        intro y hy
        by_contra hn
        exact hY ⟨y, hy, hn⟩
      rcases fm_line hC (phiB n C pw lw I) p l β (inp C s (!bs)) hRβ hB0 hnY with
        ha2 | ⟨y, hy, hne⟩ | hc2
      · exact hq_4b2 ⟨(s, bs), mem_KA.mpr hs, Lb_mono hRβ (Lb_self hB0), ha2, Lb_self h10,
          ⟨y2, hy2, hne2⟩, Hs1⟩
      · exact hq_Bb ⟨(β, bβ), mem_KA.mpr hβ, hl1, hl2, Lb_self hB0, ⟨y, hy, hne⟩,
          fun y' hy' => hnY y' (Lb_mono hRβ hy')⟩
      · exact hq_Bc hc2
  · exact hq_4bc hc

theorem hq_of_half {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) (p : Fin N) (l : Fin M) (hI : I p l)
    (h : HalfC n C pw lw I Tr p l) : HQ n C pw lw I Tr (p, l) := by
  rcases h with h | h | h | h | h | h | h
  · exact hq_of_D0 hS p l h
  · exact hq_of_C15 hS p l h
  · exact hq_of_C14 hS p l h
  · exact hq_of_C1 hS p l h
  · exact hq_of_C2h hS p l hI h
  · exact hq_of_C4a hS p l hI h
  · exact hq_of_C4b hS p l hI h

theorem half {n : ℕ} {C : Circuit} {N M : ℕ} {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {Tr : Finset (Fin N) → Finset (Fin M) → ℕ → Prop} (hS : Sys n C N M pw lw I Tr) :
    Bd (fun e : Fin N × Fin M => I e.1 e.2 ∧
      Prim n C (GPf n C pw I e.1 e.2) (GLf n C lw I e.1 e.2))
      (24 * (KA C).card + 19 * (KO C).card) :=
  Bd_mono (fun e he => hq_of_half hS e.1 e.2 he.1 (cover_prim hS e.1 e.2 he.2)) (bd_HQ hS)

-- fragment f10_main
theorem Bd_ncard {X : Type} [Finite X] {P : X → Prop} {k : ℕ} (h : Bd P k) :
    {e | P e}.ncard ≤ k := by
  classical
  have hfin : {e | P e}.Finite := Set.toFinite _
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine h _ ?_
  intro e he
  exact (Set.Finite.mem_toFinset hfin).mp he

theorem Bd_swap {α β : Type} {P : β × α → Prop} {k : ℕ} (h : Bd P k) :
    Bd (fun e : α × β => P e.swap) k := by
  classical
  intro S hS
  have h1 : (S.image Prod.swap).card = S.card :=
    Finset.card_image_of_injective S Prod.swap_injective
  have h2 := h (S.image Prod.swap) (fun e he => by
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    exact hS e' he')
  omega

theorem core (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hpw : Function.Injective pw) (hlw : Function.Injective lw)
    (hne : ∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) (hpn : ∀ p2 : Fin N, pw p2 < n)
    (hln : ∀ l2 : Fin M, lw l2 < n)
    (h4 : ∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5))
    (hsound : (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false))
    (hread : (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ Rr n C (n + j6) C.output ∧ Tt n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ Tt n C ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ))) :
    {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 96 * C.gates.length := by
  have hS : Sys n C N M pw lw I (fun P Y w =>
      W n C (fun k : Fin n => decide (k.val ∈ P.image pw ∪ Y.image lw)) w = true) := by
    refine ⟨hAO, hpw, hlw, hpn, hln, h4, ?_, ?_, ?_, ?_, ?_⟩
    · intro P Y x hx
      show W n C _ (pw x) = true
      rw [W_input n C _ (pw x) (hpn x)]
      exact decide_eq_true (Finset.mem_union_left _ (Finset.mem_image_of_mem pw hx))
    · intro P Y y hy
      show W n C _ (lw y) = true
      rw [W_input n C _ (lw y) (hln y)]
      exact decide_eq_true (Finset.mem_union_right _ (Finset.mem_image_of_mem lw hy))
    · intro P Y a b h ha
      exact path_up n C _ a b h ha
    · intro P Y j hj h0 h1
      rw [inp_false] at h0
      rw [inp_true] at h1
      exact and_up n C _ hAO j hj.1 hj.2 h0 h1
    · intro P Y hP hY h
      by_contra hcon
      have hno : ∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3 :=
        fun p3 hp3 l3 hl3 hI => hcon ⟨p3, hp3, l3, hl3, hI⟩
      have h2 := hsound P Y hP hY hno
      have h1 : PEqualNP.MetaComplexity.circuitFun n C
          (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = true := h
      rw [h1] at h2
      exact Bool.noConfusion h2
  have hbA := half hS
  have hbB := half (Sys_swap hS)
  have hE1 : {e : Fin N × Fin M | I e.1 e.2 ∧
      Prim n C (GPf n C pw I e.1 e.2) (GLf n C lw I e.1 e.2)}.ncard ≤
      24 * (KA C).card + 19 * (KO C).card := Bd_ncard hbA
  have conv : ∀ e : Fin N × Fin M,
      (I e.1 e.2 ∧ Prim n C (GLf n C lw I e.1 e.2) (GPf n C pw I e.1 e.2)) →
      ((fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2 ∧
        Prim n C (GPf n C lw (fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2)
          (GLf n C pw (fun (y : Fin M) (x : Fin N) => I x y) e.swap.1 e.swap.2)) :=
    fun e he => he
  have hE2 : {e : Fin N × Fin M | I e.1 e.2 ∧
      Prim n C (GLf n C lw I e.1 e.2) (GPf n C pw I e.1 e.2)}.ncard ≤
      24 * (KA C).card + 19 * (KO C).card := Bd_ncard (Bd_mono conv (Bd_swap hbB))
  have key : ∀ S : Set (Fin N × Fin M), (∀ e ∈ S,
      e ∈ {e : Fin N × Fin M | I e.1 e.2 ∧
        Prim n C (GPf n C pw I e.1 e.2) (GLf n C lw I e.1 e.2)} ∪
      {e : Fin N × Fin M | I e.1 e.2 ∧
        Prim n C (GLf n C lw I e.1 e.2) (GPf n C pw I e.1 e.2)}) →
      S.ncard ≤ 2 * (24 * (KA C).card + 19 * (KO C).card) := by
    intro S hsub
    have h1 := Set.ncard_le_ncard (fun e he => hsub e he) (Set.toFinite _)
    have h2 := Set.ncard_union_le {e : Fin N × Fin M | I e.1 e.2 ∧
        Prim n C (GPf n C pw I e.1 e.2) (GLf n C lw I e.1 e.2)}
      {e : Fin N × Fin M | I e.1 e.2 ∧
        Prim n C (GLf n C lw I e.1 e.2) (GPf n C pw I e.1 e.2)}
    omega
  have hOR : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard =
      (orS C).card := by
    have hset : {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or} =
        ((orS C : Finset ℕ) : Set ℕ) := by
      ext j
      simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_orS, OrG]
    rw [hset, Set.ncard_coe_finset]
  have h10 := l2410 n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound (Rr n C) rfl (Tt n C) rfl
    hread
  have hfin : 4 * {jo : ℕ | jo < C.gates.length ∧ (gateAt C jo).op = GateOp.or}.ncard +
      2 * (24 * (KA C).card + 19 * (KO C).card) ≤ 96 * C.gates.length := by
    have a := card_KA C
    have b := card_KO C
    have c := and_or_card hAO
    rw [hOR]
    omega
  refine le_trans h10 (le_trans (Nat.add_le_add_left (key _ ?_) _) hfin)
  intro e he
  obtain ⟨hI, hn7, hn9⟩ := he
  obtain ⟨L6, ⟨j6, La, Lb, hj6, hop6, hR6, hTa, hTb, hL⟩, hvars, hcp, hcl⟩ := hread e.1 e.2 hI
  subst hL
  have hleaf : ∀ g ∈ La ++ Lb, Rr n C g.2 g.1 := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact Tt_leafR hTa g h
    · exact Tt_leafR hTb g h
  have hk : LOK (pw e.1) (lw e.2) (GPf n C pw I e.1 e.2) (GLf n C lw I e.1 e.2) (La ++ Lb) := by
    intro g hg
    have hRg := hleaf g hg
    rcases hvars g hg with h | h
    · left
      refine ⟨h, ?_, ?_⟩
      · rw [← h]
        exact hRg
      · by_cases hd : ∃ q, Rr n C (pw q) g.1 ∧ ¬ I q e.2
        · exact Or.inr hd
        · left
          intro x hx
          by_contra hxp
          apply hn7
          refine ⟨La ++ Lb, ⟨j6, La, Lb, hj6, hop6, hR6, hTa, hTb, rfl⟩, hvars, hcp, hcl, g, hg,
            h, ?_, ?_⟩
          · intro q8 hq8
            by_contra hnI
            exact hd ⟨q8, hq8, hnI⟩
          · have hsub : ({x, e.1} : Set (Fin N)) ⊆ {r8 : Fin N | Rr n C (pw r8) g.1} := by
              intro r hr
              rcases Set.mem_insert_iff.mp hr with h' | h'
              · rw [h']
                exact hx
              · rw [Set.mem_singleton_iff.mp h']
                show Rr n C (pw e.1) g.1
                rw [← h]
                exact hRg
            calc 2 = ({x, e.1} : Set (Fin N)).ncard := (Set.ncard_pair hxp).symm
              _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    · right
      refine ⟨h, ?_, ?_⟩
      · rw [← h]
        exact hRg
      · by_cases hd : ∃ y, Rr n C (lw y) g.1 ∧ ¬ I e.1 y
        · exact Or.inr hd
        · left
          intro x hx
          by_contra hxp
          apply hn9
          refine ⟨La ++ Lb, ⟨j6, La, Lb, hj6, hop6, hR6, hTa, hTb, rfl⟩, hvars, hcp, hcl, g, hg,
            h, ?_, ?_⟩
          · intro q8 hq8
            by_contra hnI
            exact hd ⟨q8, hq8, hnI⟩
          · have hsub : ({x, e.2} : Set (Fin M)) ⊆ {r8 : Fin M | Rr n C (lw r8) g.1} := by
              intro r hr
              rcases Set.mem_insert_iff.mp hr with h' | h'
              · rw [h']
                exact hx
              · rw [Set.mem_singleton_iff.mp h']
                show Rr n C (lw e.2) g.1
                rw [← h]
                exact hRg
            calc 2 = ({x, e.2} : Set (Fin M)).ncard := (Set.ncard_pair hxp).symm
              _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcp' : cnt (pw e.1) (La ++ Lb) = 1 ∨ cnt (pw e.1) (La ++ Lb) = 2 := by
    have h := hcp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h
  have hcl' : cnt (lw e.2) (La ++ Lb) = 1 ∨ cnt (lw e.2) (La ++ Lb) = 2 := by
    have h := hcl
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h
  have hprim := prim_of_tree (hne e.1 e.2) j6 ⟨hj6, hop6⟩ hR6 La Lb
    (by rw [inp_false]; exact hTa) (by rw [inp_true]; exact hTb) hk hcp' hcl'
  rcases hprim with h | h
  · exact Or.inl ⟨hI, h⟩
  · exact Or.inr ⟨hI, h⟩

theorem main_aux : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 112 * C.size := by
  intro n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound R hR T hT hread
  subst hR
  subst hT
  have h := core n N M pw lw I C hAO hpw hlw hne hpn hln h4 hsound hread
  show _ ≤ 112 * C.gates.length
  omega

end PEqualNP.Outside.L_meta_2424

theorem PEqualNP.Outside.L_meta_2424 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (p4 p5 : Fin N) (l4 l5 : Fin M), p4 ≠ p5 → l4 ≠ l5 → ¬ (I p4 l4 ∧ I p5 l4 ∧ I p4 l5 ∧ I p5 l5)) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → (∀ (p6 : Fin N) (l6 : Fin M), I p6 l6 → ∃ L6 : List (ℕ × ℕ), (∃ (j6 : ℕ) (La6 Lb6 : List (ℕ × ℕ)), j6 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ R (n + j6) C.output ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 0 0) La6 ∧ T ((PEqualNP.MetaComplexity.NestedCover.gateAt C j6).inputs.getD 1 0) Lb6 ∧ L6 = La6 ++ Lb6) ∧ (∀ g6 ∈ L6, g6.2 = pw p6 ∨ g6.2 = lw l6) ∧ (L6.filter (fun e6 => decide (e6.2 = pw p6))).length ∈ ({1, 2} : Finset ℕ) ∧ (L6.filter (fun f6 => decide (f6.2 = lw l6))).length ∈ ({1, 2} : Finset ℕ)) → {ei : Fin N × Fin M | I ei.1 ei.2}.ncard ≤ 112 * C.size :=
  PEqualNP.Outside.L_meta_2424.main_aux
