import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1649
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]


def singletonInput {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

def outsideSupport {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) :=
  support C w \ R

def liveInputs {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) (g : Gate) :=
  g.inputs.toFinset.filter fun r => r < w ∧ (outsideSupport C R r).Nonempty

def branches {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ h : w - n < C.gates.length,
    C.gates[w - n].op = GateOp.or ∧
      2 ≤ (liveInputs C R w C.gates[w - n]).card

noncomputable def charged {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Ico n (n + C.size)).erase z).filter fun w =>
    outsideSupport C R w ⊆ S ∧ 2 ≤ (outsideSupport C R w).card ∧ branches C R w

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma and_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.and) :
    value C x w = false ↔ ∃ r ∈ C.gates[w - n].inputs, w ≤ r ∨ value C x r = false := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hf⟩
    by_cases h' : r < w
    · exact ⟨r, hr, Or.inr (by simpa [h'] using hf)⟩
    · exact ⟨r, hr, Or.inl (by omega)⟩
  · rintro ⟨r, hr, hf | hf⟩
    · exact ⟨r, hr, by simp [show ¬ r < w by omega]⟩
    · exact ⟨r, hr, by simp [hf]⟩

lemma outside_mono {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (x y : Fin n → Bool) (hx : value ⟨gates, 0⟩ x (n+j.val) = true)
    (hy : value ⟨gates, 0⟩ y (n+j.val) = true)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  rw [← replC_eq gates j 0 x hx w, ← replC_eq gates j 0 y hy w]
  exact value_mono _ (replC_gates gates j hops hu) x y hxy w

lemma outside_input_data {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (y : Fin n → Bool)
    (w : ℕ) (hw : n ≤ w) (h : w - n < C.gates.length)
    (hops : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or)
    (hlen : C.gates[w - n].inputs.length ≤ 2)
    (hy : value C y w = false) (hne : (outsideSupport C R w).Nonempty) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < w ∧ value C y r = false) ∧
      outsideSupport C R w ⊆ P.biUnion (outsideSupport C R) ∧
      P.card ≤ 2 ∧ (2 ≤ P.card → branches C R w) := by
  classical
  rcases hops with hop | hop
  · obtain ⟨r, hr, hbad⟩ := (and_false C y w hw h hop).mp hy
    have hlt : r < w := by
      by_contra! hrw
      obtain ⟨p, hp⟩ := hne
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hbad' := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inl hrw⟩
      change value C (singletonInput p) w = true at hp'
      simp [hbad'] at hp'
    refine ⟨{r}, ?_, ?_, by simp, by simp⟩
    · intro a ha
      have : a = r := Finset.mem_singleton.mp ha
      subst a
      exact ⟨hlt, hbad.resolve_left (by omega)⟩
    · intro p hp
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hpr : value C (singletonInput p) r = true := by
        by_contra! hr'
        have hr'' : value C (singletonInput p) r = false := by simpa using hr'
        have hn := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inr hr''⟩
        change value C (singletonInput p) w = true at hp'
        simp [hn] at hp'
      simpa [outsideSupport] using
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hpr, (Finset.mem_sdiff.mp hp).2⟩
  · let P := liveInputs C R w C.gates[w - n]
    refine ⟨P, ?_, ?_, ?_, fun hP => ⟨h,hop,hP⟩⟩
    · intro r hr
      have ⟨hri, hlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hlt, Bool.eq_false_iff.mpr ?_⟩
      intro hrt
      have he := (or_value C y w hw h hop).mpr ⟨r,List.mem_toFinset.mp hri,hlt,hrt⟩
      simp [hy] at he
    · intro p hp
      have hpt := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C (singletonInput p) w hw h hop).mp hpt
      have hpr : p ∈ outsideSupport C R r :=
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hv, (Finset.mem_sdiff.mp hp).2⟩
      exact Finset.mem_biUnion.mpr ⟨r,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt, ⟨p,hpr⟩⟩, hpr⟩
    · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)

lemma outside_sub {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool)
    (hy : ∀ p, p ∉ R → p ∉ S → y p = true)
    (hm : ∀ p, p ∉ R → y p = true → ∀ w,
      value C (singletonInput p) w = true → value C y w = true)
    (w : ℕ) (hw : value C y w = false) :
    outsideSupport C R w ⊆ S := by
  intro p hp
  obtain ⟨hs, hr⟩ := Finset.mem_sdiff.mp hp
  by_contra hs'
  have := hm p hr (hy p hr hs') w ((mem_support C w p).mp hs)
  simp [hw] at this

-- Trace the outside singleton inputs backward through wires that are false on y.
lemma frontier {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    ∀ (t : ℕ) (B : Finset ℕ), (∀ w ∈ B, value C y w = false) →
      (∀ w ∈ B, 2 ≤ (outsideSupport C R w).card → w < t) →
      ∃ F : Finset ℕ, B.biUnion (outsideSupport C R) ⊆ F.biUnion (outsideSupport C R) ∧
        (∀ w ∈ F, (outsideSupport C R w).card ≤ 1) ∧
        F.card ≤ B.card + ((charged C R S z).filter (· < t)).card := by
  classical
  intro t
  induction t with
  | zero =>
    intro B _ hlt
    refine ⟨B, Finset.Subset.rfl, ?_, by omega⟩
    intro w hw
    have := hlt w hw
    omega
  | succ t ih =>
    intro B hfalse hlt
    by_cases hcase : t ∈ B ∧ 2 ≤ (outsideSupport C R t).card
    · obtain ⟨ht, hs⟩ := hcase
      have hs' := hs.trans (Finset.card_le_card (Finset.sdiff_subset (s := support C t) (t := R)))
      obtain ⟨hn, hC⟩ := support_gate C t hs'
      have hi : t - n < C.gates.length := by unfold Circuit.size at hC; omega
      have hne : t ≠ z := by intro e; have := hfalse t ht; simp [e, hz] at this
      obtain ⟨hop, hlen⟩ := hops t hn hi hne
      obtain ⟨P, hP, hcover, hcard, hb⟩ :=
        outside_input_data C R y t hn hi hop hlen (hfalse t ht)
          (Finset.card_pos.mp (by omega))
      let B' := B.erase t ∪ P
      have hf' (w) (hw : w ∈ B') : value C y w = false := by
        rcases Finset.mem_union.mp hw with h | h
        · exact hfalse w (Finset.mem_erase.mp h).2
        · exact (hP w h).2
      have ht' (w) (hw : w ∈ B') (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne, hin⟩ := Finset.mem_erase.mp h
          have := hlt w hin hsw
          omega
        · exact (hP w h).1
      obtain ⟨F, hFsub, hFs, hFc⟩ := ih B' hf' ht'
      refine ⟨F, ?_, hFs, ?_⟩
      · intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        apply hFsub
        by_cases he : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), hpw⟩
      · have hbc := Finset.card_union_le (B.erase t) P
        change B'.card ≤ _ at hbc
        have he := Finset.card_erase_add_one ht
        let G := charged C R S z
        have hinc : G.filter (· < t) ⊆ G.filter (· < t + 1) := by
          intro w hw
          obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hm, by omega⟩
        by_cases hp : 2 ≤ P.card
        · have hg : t ∈ G :=
            Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr ⟨hn,hC⟩⟩,
              hsub t (hfalse t ht), hs, hb hp⟩
          have hinc' : insert t (G.filter (· < t)) ⊆ G.filter (· < t + 1) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_filter.mpr ⟨hg, by omega⟩
            · exact hinc hw
          have hfin := Finset.card_le_card hinc'
          rw [Finset.card_insert_of_notMem (by simp)] at hfin
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
        · have hfin := Finset.card_le_card hinc
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
    · have hlt' (w) (hw : w ∈ B) (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        have := hlt w hw hsw
        have hne : w ≠ t := by intro e; subst w; exact hcase ⟨hw,hsw⟩
        omega
      obtain ⟨F, hF, hFs, hFc⟩ := ih B hfalse hlt'
      refine ⟨F, hF, hFs, hFc.trans (Nat.add_le_add_left (Finset.card_le_card ?_) _)⟩
      intro w hw
      obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hm, by omega⟩

lemma charged_count {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (o z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hout : value C y o = false) (hsupport : support C o = S)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    (S \ R).card - 1 ≤ (charged C R S z).card := by
  have hlt (w) (hw : w ∈ ({o} : Finset ℕ)) (h : 2 ≤ (outsideSupport C R w).card) :
      w < n + C.size := by
    exact (support_gate C w (h.trans (Finset.card_le_card Finset.sdiff_subset))).2
  obtain ⟨F, hFsub, hFs, hFc⟩ := frontier C R S z y hz hsub hops
    (n + C.size) {o} (by intro w hw; simpa using (Finset.mem_singleton.mp hw) ▸ hout) hlt
  have h1 := Finset.card_le_card hFsub
  simp [outsideSupport, hsupport] at h1
  have h2 := Finset.card_biUnion_le_card_mul F (outsideSupport C R) 1 hFs
  have h3 := Finset.card_filter_le (charged C R S z) (fun w => w < n + C.size)
  simp only [Nat.mul_one] at h2
  simp only [Finset.card_singleton] at hFc
  omega

lemma bool_contra {a : Bool} (h1 : a = true) (h2 : a = false) : False := by
  rw [h1] at h2
  exact Bool.noConfusion h2

lemma getElem_idx (gates : List Gate) (k k' : ℕ) (hk : k < gates.length)
    (hk' : k' < gates.length) (e : k = k') : gates[k] = gates[k'] := by
  subst e
  rfl

lemma replC_low {n : ℕ} (gates : List Gate) (i0 : ℕ) (o : ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw0 : w < n + i0) :
    value (replC gates i0) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · rw [orig_value gates o x w (by omega) hw,
        replC_other gates i0 x w (by omega) hw (by omega)]
      apply repl_eval_congr
      intro r _
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0) x w (by rw [replC_size]; omega)]

lemma low_mono {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ)
    (hw : w < n + j.val) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  rw [← replC_low gates j.val 0 x w hw, ← replC_low gates j.val 0 y w hw]
  exact value_mono _ (replC_gates gates j hops hu) x y hxy w

lemma not_value {n : ℕ} (gates : List Gate) (j : Fin gates.length) (hwire : ℕ) (rr : List ℕ)
    (hj : (gates.get j).op = GateOp.not) (hin : (gates.get j).inputs = hwire :: rr)
    (hlt : hwire < n + j.val) (x : Fin n → Bool) :
    value ⟨gates, 0⟩ x (n + j.val) = !(value ⟨gates, 0⟩ x hwire) := by
  have key : ∀ (k : ℕ) (hk : k < gates.length), k = j.val →
      (gates[k]).op.eval ((gates[k]).inputs.map fun r =>
        if r < n + j.val then value ⟨gates, 0⟩ x r else false) =
        !(value ⟨gates, 0⟩ x hwire) := by
    intro k hk ek
    subst ek
    have e : gates[j.val] = gates.get j := rfl
    rw [e, hj, hin]
    simp [GateOp.eval, hlt]
  rw [orig_value gates 0 x (n + j.val) (by omega) (by omega)]
  exact key _ _ (by omega)

lemma reader_not_charged {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z z' w : ℕ)
    (hmem : w ∈ charged C R S z') (hn : n ≤ w) (h : w - n < C.gates.length)
    (hzin : z ∈ C.gates[w - n].inputs) (hzw : z < w)
    (p : Fin n) (hpR : p ∉ R) (hpS : p ∉ S)
    (hzp : value C (singletonInput p) z = true) : False := by
  classical
  obtain ⟨_, hsub, _, ⟨h', hop, _⟩⟩ := Finset.mem_filter.mp hmem
  have hwp : value C (singletonInput p) w = true :=
    (or_value C (singletonInput p) w hn h hop).mpr ⟨z, hzin, hzw, hzp⟩
  have hps : p ∈ outsideSupport C R w :=
    Finset.mem_sdiff.mpr ⟨(mem_support C w p).mpr hwp, hpR⟩
  exact hpS (hsub hps)

noncomputable def Tset {n : ℕ} (Li R Sh : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact if (Li ∩ R ∩ Sh).Nonempty then ∅ else Sh

lemma Tset_sub {n : ℕ} (Li R Sh : Finset (Fin n)) : Tset Li R Sh ⊆ Sh := by
  classical
  unfold Tset
  split_ifs
  · exact Finset.empty_subset _
  · exact Finset.Subset.refl _

lemma Tset_ne {n : ℕ} (Li R Sh : Finset (Fin n)) (p : Fin n) (hp : p ∈ Tset Li R Sh) :
    ¬ (Li ∩ R ∩ Sh).Nonempty := by
  classical
  intro hne
  unfold Tset at hp
  rw [if_pos hne] at hp
  exact absurd hp (Finset.notMem_empty p)

lemma Tset_eq {n : ℕ} (Li R Sh : Finset (Fin n)) (h : ¬ (Li ∩ R ∩ Sh).Nonempty) :
    Tset Li R Sh = Sh := by
  classical
  unfold Tset
  rw [if_neg h]

def mixedT {n : ℕ} (C : Circuit) (R S T : Finset (Fin n)) (w : ℕ) : Prop :=
  support C w ⊆ S ∪ T ∧ (outsideSupport C R w).Nonempty ∧
    (∃ p ∈ support (n := n) C w, p ∈ S ∧ p ∈ R) ∧ value C (fun _ : Fin n => false) w = false

lemma mixedT_card {n : ℕ} (C : Circuit) (R S T : Finset (Fin n)) (w : ℕ)
    (hw : mixedT C R S T w) : 2 ≤ (support (n := n) C w).card := by
  obtain ⟨_, ⟨u, hu⟩, ⟨p, hps, _, hpR⟩, _⟩ := hw
  obtain ⟨hus, huR⟩ := Finset.mem_sdiff.mp hu
  exact Finset.one_lt_card.mpr ⟨u, hus, p, hps, fun h => huR (h ▸ hpR)⟩

-- The first wire that is mixed for a line is a gate, not the NOT gate, not a branching OR,
-- and does not read the NOT gate.
lemma entryT_spec {n : ℕ} (C : Circuit) (R S T : Finset (Fin n)) (z : ℕ)
    (hzero : value C (fun _ : Fin n => false) z = true)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hopz : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or))
    (hT : (∀ p : Fin n, value C (singletonInput p) z = false → p ∈ T) ∨
      (∀ p : Fin n, p ∈ S → p ∈ R → value C (singletonInput p) z = false))
    (w : ℕ) (hmix : mixedT C R S T w) (hmin : ∀ r, r < w → ¬ mixedT C R S T r) :
    (n ≤ w ∧ w < n + C.size) ∧ w ≠ z ∧ ¬ branches C R w ∧
      ¬ (∃ h : w - n < C.gates.length, z ∈ C.gates[w - n].inputs ∧ z < w) := by
  classical
  have hcard2 := mixedT_card C R S T w hmix
  obtain ⟨hsub, ⟨u, hu⟩, ⟨p, hps, hpS, hpR⟩, hw0⟩ := hmix
  obtain ⟨hus, huR⟩ := Finset.mem_sdiff.mp hu
  have ⟨hn, hC⟩ := support_gate C w hcard2
  have hne : w ≠ z := by
    intro h
    rw [h] at hw0
    exact bool_contra hzero hw0
  refine ⟨⟨hn, hC⟩, hne, ?_, ?_⟩
  · rintro ⟨h, hop, hb⟩
    let g := C.gates[w - n]
    obtain ⟨r,hr,hrw,hrt⟩ :=
      (or_value C (singletonInput p) w hn h hop).mp ((mem_support C w p).mp hps)
    have hfilter : liveInputs C R w g = g.inputs.toFinset := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      exact (List.toFinset_card_le _).trans ((hlen _ (List.getElem_mem _)).trans hb)
    have hout : (outsideSupport C R r).Nonempty :=
      (Finset.mem_filter.mp (show r ∈ liveInputs C R w g by
        rw [hfilter]; exact List.mem_toFinset.mpr hr)).2.2
    have hrsub : support (n := n) C r ⊆ support C w := by
      intro p' hp'
      exact (mem_support C w p').mpr ((or_value C (singletonInput p') w hn h hop).mpr
        ⟨r,hr,hrw,(mem_support C r p').mp hp'⟩)
    have hzero' : value C (fun _ : Fin n => false) r = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have := (or_value C _ w hn h hop).mpr ⟨r,hr,hrw,ht⟩
      exact bool_contra this hw0
    exact hmin r hrw ⟨hrsub.trans hsub, hout, ⟨p, (mem_support C r p).mpr hrt, hpS, hpR⟩, hzero'⟩
  · rintro ⟨h, hzin, hzw⟩
    rcases hopz w hn h hne with hop | hop
    · have hall : ∀ r ∈ C.gates[w - n].inputs, r < w ∧
          ∀ x : Fin n → Bool, value C x w = true → value C x r = true := by
        intro r hr
        have hrw : r < w := by
          by_contra hge
          have hf := (and_false C (singletonInput u) w hn h hop).mpr ⟨r, hr, Or.inl (by omega)⟩
          exact bool_contra ((mem_support C w u).mp hus) hf
        refine ⟨hrw, fun x hx => ?_⟩
        by_contra hf
        have hf' : value C x r = false := by simpa using hf
        exact bool_contra hx ((and_false C x w hn h hop).mpr ⟨r, hr, Or.inr hf'⟩)
      obtain ⟨a, ha, hbad⟩ := (and_false C (fun _ : Fin n => false) w hn h hop).mp hw0
      have haf : value C (fun _ : Fin n => false) a = false := by
        rcases hbad with hbad | hbad
        · have := (hall a ha).1
          omega
        · exact hbad
      have haz : a ≠ z := by
        intro e
        rw [e] at haf
        exact bool_contra hzero haf
      have hpair : ∀ r ∈ C.gates[w - n].inputs, r = z ∨ r = a := by
        intro r hr
        have hsubset : ({z, a} : Finset ℕ) ⊆ C.gates[w - n].inputs.toFinset := by
          intro t ht
          rcases Finset.mem_insert.mp ht with e | ht
          · rw [e]; exact List.mem_toFinset.mpr hzin
          · rw [Finset.mem_singleton.mp ht]; exact List.mem_toFinset.mpr ha
        have hc : C.gates[w - n].inputs.toFinset.card ≤ ({z, a} : Finset ℕ).card := by
          rw [Finset.card_pair (Ne.symm haz)]
          exact (List.toFinset_card_le _).trans (hlen _ (List.getElem_mem _))
        have heq := Finset.eq_of_subset_of_card_le hsubset hc
        have hmem : r ∈ ({z, a} : Finset ℕ) := by
          rw [heq]; exact List.mem_toFinset.mpr hr
        rcases Finset.mem_insert.mp hmem with e | e
        · exact Or.inl e
        · exact Or.inr (Finset.mem_singleton.mp e)
      have hpz : value C (singletonInput p) z = true :=
        (hall z hzin).2 _ ((mem_support C w p).mp hps)
      apply hmin a (hall a ha).1
      refine ⟨?_, ⟨u, Finset.mem_sdiff.mpr
          ⟨(mem_support C a u).mpr ((hall a ha).2 _ ((mem_support C w u).mp hus)), huR⟩⟩,
        ⟨p, (mem_support C a p).mpr ((hall a ha).2 _ ((mem_support C w p).mp hps)), hpS, hpR⟩,
        haf⟩
      intro v hv
      by_contra hvn
      have hwv : value C (singletonInput v) w = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact hvn (hsub ((mem_support C w v).mpr ht))
      obtain ⟨r, hr, hrbad⟩ := (and_false C (singletonInput v) w hn h hop).mp hwv
      have hrf : value C (singletonInput v) r = false := by
        rcases hrbad with hb | hb
        · have := (hall r hr).1
          omega
        · exact hb
      rcases hpair r hr with e | e
      · rw [e] at hrf
        rcases hT with hT | hT
        · exact hvn (Finset.mem_union_right _ (hT v hrf))
        · exact bool_contra hpz (hT p hpS hpR)
      · rw [e] at hrf
        exact bool_contra ((mem_support C a v).mp hv) hrf
    · have := (or_value C (fun _ : Fin n => false) w hn h hop).mpr ⟨z, hzin, hzw, hzero⟩
      exact bool_contra this hw0


theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j : Fin gates.length) (hw : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    hw < N + (j : ℕ) → (∃ r : List ℕ, (gates.get j).inputs = hw :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∃ x : Fin N → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn x) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length ∧
    (N ≤ hw → (Finset.univ.filter (fun p : Fin N => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true)).card ≤ 1 →
      N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length) := by
  intro q N L i0 hq hN hcard hinter _ gates o j hwire hg htopo hjn hunique hlt hin hcorrect _ hfalse
  generalize hKdef : (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)) = Kf
  have hKf : ∀ i ∈ Kf, (N + j.val) ∈ (gates.get i).inputs := by
    intro i hi
    rw [← hKdef] at hi
    exact (Finset.mem_filter.mp hi).2
  classical
  obtain ⟨rr, hin⟩ := hin
  let R : Finset (Fin N) := L i0
  let C : Circuit := ⟨gates, 0⟩
  let z := N + j.val
  have hzval (x : Fin N → Bool) : value C x z = !(value C x hwire) :=
    not_value gates j hwire rr hjn hin hlt x
  have hhR (x : Fin N → Bool) (hx : ∀ v ∈ R, x v = false) : value C x hwire = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have hxy : ∀ p, x p = true → (fun v : Fin N => decide (v ∉ L i0)) p = true := by
      intro p hp
      show decide (p ∉ L i0) = true
      apply decide_eq_true
      intro hpR
      exact bool_contra hp (hx p hpR)
    have h1 := low_mono gates j hg hunique x _ hxy hwire hlt ht
    exact bool_contra h1 hfalse
  have hz (x : Fin N → Bool) (hx : ∀ v ∈ R, x v = false) : value C x z = true := by
    have h := hzval x
    rw [hhR x hx] at h
    exact h
  have hop (w) (hn : N ≤ w) (hw : w - N < C.gates.length) (hne : w ≠ z) :
      (C.gates[w - N].op = GateOp.and ∨ C.gates[w - N].op = GateOp.or) ∧
      C.gates[w - N].inputs.length ≤ 2 := by
    have h := hg C.gates[w - N] (List.getElem_mem _)
    refine ⟨?_, h.2⟩
    rcases h.1 with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · have he := congrArg Fin.val (hunique ⟨w - N, hw⟩ e)
      change w - N = j.val at he
      exact False.elim (hne (by dsimp [z]; omega))
  have ho (i) (x : Fin N → Bool) :
      value C x (o i) = decide (∃ v ∈ L i, x v = true) := hcorrect i x
  have hsp (i) : support C (o i) = L i := by
    ext p
    rw [mem_support, ← show singletonInput p = (fun v => decide (v = p)) from rfl,
      ho i (singletonInput p)]
    simp [singletonInput]
  have hpair : ∀ i i' : Fin N, i ≠ i' → (L i ∩ L i').card ≤ 1 :=
    fun i i' h => (hinter i i' h).le
  have counts (i) : (L i \ R).card - 1 ≤ (charged C R (L i) z).card := by
    let y : Fin N → Bool := fun p => decide (p ∉ R ∧ p ∉ L i)
    have hy : ∀ p ∈ R, y p = false := by intro p hp; simp [y, hp]
    apply charged_count C R (L i) (o i) z y (hz y hy) _ (hsp i) _ hop
    · rw [ho]
      apply decide_eq_false
      rintro ⟨p, hp, he⟩
      exact (of_decide_eq_true he).2 hp
    · apply outside_sub C R (L i) y
      · intro p hp hr; simp [y,hp,hr]
      · intro p hp hyp w
        have hsing : ∀ r ∈ R, singletonInput p r = false := by
          intro r hr
          have hne : r ≠ p := fun e => hp (e ▸ hr)
          simp [singletonInput, hne]
        apply outside_mono gates j hg hunique (singletonInput p) y (hz _ hsing) (hz _ hy) _ w
        intro v hv
        have e : v = p := of_decide_eq_true hv
        simpa [e] using hyp
  -- the gates of the line R itself: wires with all single points inside R
  let X : Finset ℕ := charged C ∅ R z
  have hXcount : q ≤ X.card := by
    let y : Fin N → Bool := fun p => decide (p ∉ R)
    have hy : ∀ p ∈ R, y p = false := by intro p hp; simp [y, hp]
    have h := charged_count C ∅ R (o i0) z y (hz y hy) (by
        rw [ho]
        apply decide_eq_false
        rintro ⟨p, hp, he⟩
        exact (of_decide_eq_true he) hp) (hsp i0) (by
        apply outside_sub C ∅ R y
        · intro p _ hr; simp [y, hr]
        · intro p _ hyp w
          have hpR : p ∉ R := of_decide_eq_true hyp
          have hsing : ∀ r ∈ R, singletonInput p r = false := by
            intro r hr
            have hne : r ≠ p := fun e => hpR (e ▸ hr)
            simp [singletonInput, hne]
          apply outside_mono gates j hg hunique (singletonInput p) y (hz _ hsing) (hz _ hy) _ w
          intro v hv
          have e : v = p := of_decide_eq_true hv
          simpa [e] using hyp) hop
    have hc : (R \ ∅).card = q + 1 := by simpa using hcard i0
    rw [hc] at h
    simpa using h
  have hXsup : ∀ w ∈ X, support C w ⊆ R := by
    intro w hw
    have h := (Finset.mem_filter.mp hw).2.1
    simpa [outsideSupport] using h
  -- single points of the wire read by the NOT gate
  let Sh : Finset (Fin N) := support C hwire
  have hsingR (p : Fin N) (hp : p ∉ R) : ∀ r ∈ R, singletonInput p r = false := by
    intro r hr
    have hne : r ≠ p := fun e => hp (e ▸ hr)
    simp [singletonInput, hne]
  have hShR : Sh ⊆ R := by
    intro p hp
    by_contra hpR
    exact bool_contra ((mem_support C hwire p).mp hp) (hhR (singletonInput p) (hsingR p hpR))
  have hz_false (p : Fin N) (hp : p ∈ Sh) : value C (singletonInput p) z = false := by
    have hh : value C (singletonInput p) hwire = true := (mem_support C hwire p).mp hp
    have h := hzval (singletonInput p)
    rw [hh] at h
    exact h
  have hz_Sh (p : Fin N) (hzf : value C (singletonInput p) z = false) : p ∈ Sh := by
    rw [hzval] at hzf
    have h2 : value C (singletonInput p) hwire = true := by simpa using hzf
    exact (mem_support C hwire p).mpr h2
  have hRc : R.card = q + 1 := hcard i0
  have hNbig : 2 * q + 2 < N := by
    have hqq : 2 * q ≤ q ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_right q hq
    omega
  have hpt (i : Fin N) : ∃ p : Fin N, p ∉ R ∧ p ∉ L i := by
    by_contra hcon
    have hall : (Finset.univ : Finset (Fin N)) ⊆ R ∪ L i := by
      intro p _
      by_contra hp
      exact hcon ⟨p, fun h => hp (Finset.mem_union_left _ h),
        fun h => hp (Finset.mem_union_right _ h)⟩
    have h1 := Finset.card_le_card hall
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_union_le R (L i)
    have h3 := hcard i
    omega
  -- the gates reading the NOT gate
  let K : Finset ℕ := Kf.image (fun i : Fin gates.length => N + i.val)
  have hKcard : K.card = Kf.card :=
    Finset.card_image_of_injective _ (fun a b hab => Fin.ext (by
      have h : N + a.val = N + b.val := hab
      omega))
  have hKspec (w : ℕ) (hwK : w ∈ K) :
      N ≤ w ∧ ∃ h : w - N < C.gates.length, z ∈ C.gates[w - N].inputs ∧ z < w := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hwK
    have hin' := hKf i hi
    have hidx : N + i.val - N < gates.length := by omega
    refine ⟨by omega, hidx, ?_, htopo i _ hin'⟩
    have hmem : (N + j.val) ∈ (gates[i.val]'i.isLt).inputs := hin'
    rw [← getElem_idx gates (N + i.val - N) i.val hidx i.isLt (by omega)] at hmem
    exact hmem
  have hKX (R' S' : Finset (Fin N)) (z' : ℕ) (p : Fin N) (hpR : p ∉ R) (hpR' : p ∉ R')
      (hpS' : p ∉ S') (w : ℕ) (hwc : w ∈ charged C R' S' z') (hwK : w ∈ K) : False := by
    obtain ⟨hKn, hKh, hKin, hKlt⟩ := hKspec w hwK
    exact reader_not_charged C R' S' z z' w hwc hKn hKh hKin hKlt p hpR' hpS'
      (hz _ (hsingR p hpR))
  -- the entry gate of every other line
  have hT (i : Fin N) (hi : i ≠ i0) :
      (∀ p : Fin N, value C (singletonInput p) z = false → p ∈ Tset (L i) R Sh) ∨
      (∀ p : Fin N, p ∈ L i → p ∈ R → value C (singletonInput p) z = false) := by
    by_cases hne : (L i ∩ R ∩ Sh).Nonempty
    · right
      obtain ⟨m', hm'⟩ := hne
      obtain ⟨hm1, hm3⟩ := Finset.mem_inter.mp hm'
      intro p hpL hpR
      have e : p = m' := Finset.card_le_one.mp (hpair i i0 hi) p
        (Finset.mem_inter.mpr ⟨hpL, hpR⟩) m' hm1
      rw [e]
      exact hz_false m' hm3
    · left
      intro p hzf
      rw [Tset_eq _ _ _ hne]
      exact hz_Sh p hzf
  have hmixo (i : Fin N) (hi : i ≠ i0) : mixedT C R (L i) (Tset (L i) R Sh) (o i) := by
    have h1 : (L i ∩ R).card = 1 := hinter i i0 hi
    have h2 := Finset.card_sdiff_add_card_inter (L i) R
    have h3 := hcard i
    have hne1 : (L i \ R).Nonempty := Finset.card_pos.mp (by omega)
    have hne2 : (L i ∩ R).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp⟩ := hne2
    obtain ⟨hp1, hp2⟩ := Finset.mem_inter.mp hp
    refine ⟨?_, ?_, ⟨p, ?_, hp1, hp2⟩, ?_⟩
    · rw [hsp]
      exact Finset.subset_union_left
    · simpa only [outsideSupport, hsp] using hne1
    · rw [hsp]
      exact hp1
    · rw [ho]
      simp
  let E : Finset ℕ := (Finset.Ico N (N + C.size)).erase z
  have hent : ∀ i : Fin N, ∃ w : ℕ, i ≠ i0 →
      (w ∈ E ∧ ¬ branches C R w ∧ w ∉ K ∧ mixedT C R (L i) (Tset (L i) R Sh) w) := by
    intro i
    by_cases hi : i = i0
    · exact ⟨0, fun h => absurd hi h⟩
    · have hex : ∃ w, mixedT C R (L i) (Tset (L i) R Sh) w := ⟨o i, hmixo i hi⟩
      refine ⟨Nat.find hex, fun _ => ?_⟩
      obtain ⟨⟨hn, hC⟩, hne, hnb, hnr⟩ := entryT_spec C R (L i) (Tset (L i) R Sh) z
        (hz _ (by simp)) (fun g hg' => (hg g hg').2)
        (fun w hn h hne => (hop w hn h hne).1) (hT i hi) (Nat.find hex) (Nat.find_spec hex)
        (fun r hr => Nat.find_min hex hr)
      refine ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr ⟨hn, hC⟩⟩, hnb, ?_, Nat.find_spec hex⟩
      intro hK
      obtain ⟨_, hKh, hKin, hKlt⟩ := hKspec _ hK
      exact hnr ⟨hKh, hKin, hKlt⟩
  choose e he using hent
  have hapart : ∀ i i' : Fin N, i ≠ i' → ∀ w : ℕ, mixedT C R (L i) (Tset (L i) R Sh) w →
      mixedT C R (L i') (Tset (L i') R Sh) w → False := by
    intro i i' hii w h1 h2
    obtain ⟨hsub, ⟨u, hu⟩, ⟨p, hps, hpS, hpR⟩, _⟩ := h1
    obtain ⟨hsub', _, ⟨p', hps', hpS', hpR'⟩, _⟩ := h2
    obtain ⟨hus, huR⟩ := Finset.mem_sdiff.mp hu
    have hui : u ∈ L i := by
      rcases Finset.mem_union.mp (hsub hus) with h | h
      · exact h
      · exact absurd (hShR (Tset_sub _ _ _ h)) huR
    have hui' : u ∈ L i' := by
      rcases Finset.mem_union.mp (hsub' hus) with h | h
      · exact h
      · exact absurd (hShR (Tset_sub _ _ _ h)) huR
    have hone : ∀ a b : Fin N, a ∈ L i → a ∈ L i' → b ∈ L i → b ∈ L i' → a = b :=
      fun a b ha ha' hb hb' => Finset.card_le_one.mp (hpair i i' hii) a
        (Finset.mem_inter.mpr ⟨ha, ha'⟩) b (Finset.mem_inter.mpr ⟨hb, hb'⟩)
    have hpn : p ∉ L i' := by
      intro h
      have e1 := hone u p hui hui' hpS h
      rw [e1] at huR
      exact huR hpR
    have hpT : p ∈ Tset (L i') R Sh := by
      rcases Finset.mem_union.mp (hsub' hps) with h | h
      · exact absurd h hpn
      · exact h
    have hpn' : p' ∉ L i := by
      intro h
      have e1 := hone u p' hui hui' h hpS'
      rw [e1] at huR
      exact huR hpR'
    have hpT' : p' ∈ Tset (L i) R Sh := by
      rcases Finset.mem_union.mp (hsub hps') with h | h
      · exact absurd h hpn'
      · exact h
    exact Tset_ne _ _ _ p' hpT' ⟨p, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hpS, hpR⟩, Tset_sub _ _ _ hpT⟩⟩
  obtain ⟨En, hEn⟩ : ∃ En : Fin N → Finset ℕ, ∀ i w, w ∈ En i ↔ (i ≠ i0 ∧ w = e i) :=
    ⟨fun i => if i = i0 then ∅ else {e i}, by
      intro i w
      by_cases h : i = i0 <;> simp [h]⟩
  let U : Fin N → Finset ℕ := fun i => charged C R (L i) z ∪ En i
  have hUprop (i : Fin N) (w : ℕ) (hw : w ∈ U i) :
      (outsideSupport C R w).Nonempty ∧ 2 ≤ (support (n := N) C w).card ∧ w ∉ K ∧ w ∈ E := by
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨hE, _, h2, _⟩ := Finset.mem_filter.mp h
      refine ⟨Finset.card_pos.mp (by omega), h2.trans (Finset.card_le_card
        (Finset.sdiff_subset (s := support (n := N) C w) (t := R))), ?_, hE⟩
      intro hK
      obtain ⟨p, hp1, hp2⟩ := hpt i
      exact hKX R (L i) z p hp1 hp1 hp2 w h hK
    · obtain ⟨hi, rfl⟩ := (hEn i w).mp h
      obtain ⟨h1, _, h3, h4⟩ := he i hi
      exact ⟨h4.2.1, mixedT_card C R _ _ _ h4, h3, h1⟩
  have hdis : ((Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint U := by
    intro i _ i' _ hii
    apply Finset.disjoint_left.mpr
    intro w hi hi'
    rcases Finset.mem_union.mp hi with hi | hi <;> rcases Finset.mem_union.mp hi' with hi' | hi'
    · have ha := (Finset.mem_filter.mp hi).2
      have hb := (Finset.mem_filter.mp hi').2
      have hsub2 : outsideSupport C R w ⊆ L i ∩ L i' :=
        fun _ hp => Finset.mem_inter.mpr ⟨ha.1 hp, hb.1 hp⟩
      have := ha.2.1.trans ((Finset.card_le_card hsub2).trans (hpair i i' hii))
      omega
    · obtain ⟨hne, rfl⟩ := (hEn i' w).mp hi'
      exact (he i' hne).2.1 (Finset.mem_filter.mp hi).2.2.2
    · obtain ⟨hne, rfl⟩ := (hEn i w).mp hi
      exact (he i hne).2.1 (Finset.mem_filter.mp hi').2.2.2
    · obtain ⟨hne, rfl⟩ := (hEn i w).mp hi
      obtain ⟨hne', hw'⟩ := (hEn i' _).mp hi'
      have hm' := (he i' hne').2.2.2
      rw [← hw'] at hm'
      exact hapart i i' hii _ (he i hne).2.2.2 hm'
  have hlow (i : Fin N) : q ≤ (U i).card + (if i = i0 then q else 0) := by
    by_cases hi : i = i0
    · rw [if_pos hi]
      exact Nat.le_add_left _ _
    · rw [if_neg hi]
      have h1 : (L i ∩ R).card = 1 := hinter i i0 hi
      have h2 := Finset.card_sdiff_add_card_inter (L i) R
      have h3 := hcard i
      have h4 := counts i
      have hd : Disjoint (charged C R (L i) z) (En i) := by
        apply Finset.disjoint_left.mpr
        intro w hw hw'
        obtain ⟨_, rfl⟩ := (hEn i w).mp hw'
        exact (he i hi).2.1 (Finset.mem_filter.mp hw).2.2.2
      have h5 : (U i).card = (charged C R (L i) z).card + (En i).card :=
        Finset.card_union_of_disjoint hd
      have h6 : 0 < (En i).card := Finset.card_pos.mpr ⟨e i, (hEn i _).mpr ⟨hi, rfl⟩⟩
      omega
  have hsumU : N * q ≤ (∑ i : Fin N, (U i).card) + q := by
    have h1 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun i _ => hlow i)
    rw [Finset.sum_add_distrib] at h1
    have h2 : (∑ _i : Fin N, q) = N * q := by simp
    have h3 : (∑ i : Fin N, (if i = i0 then q else 0)) = q := by simp
    rw [h2, h3] at h1
    exact h1
  have hEcard : E.card = gates.length - 1 := by
    have hzE : z ∈ Finset.Ico N (N + C.size) :=
      Finset.mem_Ico.mpr ⟨by dsimp [z]; omega, by
        change N + j.val < N + gates.length
        omega⟩
    have h1 := Finset.card_erase_of_mem hzE
    rw [Nat.card_Ico] at h1
    change E.card = N + gates.length - N - 1 at h1
    omega
  have claim : ∀ Hs : Finset ℕ,
      (∀ w ∈ Hs, w = hwire ∧ N ≤ hwire ∧ (support (n := N) C hwire).card ≤ 1) →
      N * q + Kf.card + 1 + Hs.card ≤ gates.length := by
    intro Hs hHs
    have hXK : Disjoint X K := by
      apply Finset.disjoint_left.mpr
      intro w hw hK
      obtain ⟨p, hp1, _⟩ := hpt i0
      exact hKX ∅ R z p hp1 (Finset.notMem_empty p) hp1 w hw hK
    have hXKH : Disjoint (X ∪ K) Hs := by
      apply Finset.disjoint_left.mpr
      intro w hw hH
      obtain ⟨hweq, hNw, hc⟩ := hHs w hH
      rcases Finset.mem_union.mp hw with h | h
      · have h2 := (Finset.mem_filter.mp h).2.2.1
        rw [hweq] at h2
        have h3 := Finset.card_le_card
          (Finset.sdiff_subset (s := support (n := N) C hwire) (t := (∅ : Finset (Fin N))))
        have h4 : 2 ≤ (support (n := N) C hwire \ ∅).card := h2
        omega
      · obtain ⟨_, _, _, hKlt⟩ := hKspec w h
        have h5 : hwire < z := hlt
        omega
    have hUX (i : Fin N) : Disjoint (U i) (X ∪ K ∪ Hs) := by
      apply Finset.disjoint_left.mpr
      intro w hw hx
      obtain ⟨⟨p, hp⟩, hc2, hnK, _⟩ := hUprop i w hw
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
          exact hp2 (hXsup w hx hp1)
        · exact hnK hx
      · obtain ⟨hweq, _, hc⟩ := hHs w hx
        rw [hweq] at hc2
        omega
    have hbigd : Disjoint (Finset.univ.biUnion U) (X ∪ K ∪ Hs) := by
      rw [Finset.disjoint_biUnion_left]
      intro i _
      exact hUX i
    have hsubE : Finset.univ.biUnion U ∪ (X ∪ K ∪ Hs) ⊆ E := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
        exact (hUprop i w hi).2.2.2
      · rcases Finset.mem_union.mp hw with hw | hw
        · rcases Finset.mem_union.mp hw with hw | hw
          · exact (Finset.mem_filter.mp hw).1
          · obtain ⟨hKn, hKh, _, hKlt⟩ := hKspec w hw
            have hKh' : w - N < gates.length := hKh
            refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_Ico.mpr ⟨hKn, ?_⟩⟩
            change w < N + gates.length
            omega
        · obtain ⟨hweq, hNw, _⟩ := hHs w hw
          have h1 : hwire < N + j.val := hlt
          have h1' : hwire < z := hlt
          have hjl : j.val < gates.length := j.isLt
          rw [hweq]
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_Ico.mpr ⟨hNw, ?_⟩⟩
          · intro hbad
            omega
          · change hwire < N + gates.length
            omega
    have hc1 := Finset.card_le_card hsubE
    rw [Finset.card_union_of_disjoint hbigd, Finset.card_biUnion hdis,
      Finset.card_union_of_disjoint hXKH, Finset.card_union_of_disjoint hXK, hKcard,
      hEcard] at hc1
    have hjlt : j.val < gates.length := j.isLt
    omega
  refine ⟨?_, ?_⟩
  · have h := claim ∅ (by simp)
    simp only [Finset.card_empty] at h
    omega
  · intro hNw hthin
    have h := claim {hwire} (by
      intro w hw
      exact ⟨Finset.mem_singleton.mp hw, hNw, hthin⟩)
    simp only [Finset.card_singleton] at h
    omega

end PEqualNP.Outside.L_meta_1649

theorem PEqualNP.Outside.L_meta_1649 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j : Fin gates.length) (hw : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    hw < N + (j : ℕ) → (∃ r : List ℕ, (gates.get j).inputs = hw :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∃ x : Fin N → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn x) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length ∧
    (N ≤ hw → (Finset.univ.filter (fun p : Fin N => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true)).card ≤ 1 →
      N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length) :=
  PEqualNP.Outside.L_meta_1649.main_aux
