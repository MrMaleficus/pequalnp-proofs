import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1641
open PEqualNP.CircuitLowerBounds

abbrev V {N : ℕ} (gs : List Gate) (w : ℕ) (x : Fin N → Bool) : Bool := Circuit.eval ⟨gs,w⟩ (List.ofFn x)
abbrev base {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)
abbrev single {N : ℕ} (r : Fin N) : Fin N → Bool := fun v => decide (v = r)

namespace CoWire

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

end CoWire

lemma twoPoints {N : ℕ} (L : Fin N → Finset (Fin N)) {i t r s : Fin N}
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (ht : t ≠ i) (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s) :
    r ∉ L t ∨ s ∉ L t := by
  by_contra! h
  have hsub : ({r,s} : Finset (Fin N)) ⊆ L i ∩ L t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hr, h.1⟩
    · exact Finset.mem_inter.mpr ⟨hs, h.2⟩
  have hle := Finset.card_le_card hsub
  simp [hrs, hinter i t ht.symm] at hle

lemma offOther {N : ℕ} (gates : List Gate) (w : ℕ) (L : Fin N → Finset (Fin N))
    {i r s : Fin N} (hC : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hr : r ∈ L i) (hs : s ∈ L i) (hrs : r ≠ s)
    (h1 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = r)) = true)
    (h2 : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = s)) = true)
    (t : Fin N) (ht : t ≠ i) :
    Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
  have lift (p : Fin N) (hp : p ∉ L t)
      (hv : Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v = p)) = true) :
      Circuit.eval ⟨gates,w⟩ (List.ofFn fun v : Fin N => decide (v ∉ L t)) = true := by
    apply CoWire.mono ⟨gates,w⟩ hC (fun v : Fin N => decide (v = p)) (fun v => decide (v ∉ L t)) _ w hv
    intro v h
    simp only [decide_eq_true_eq] at h ⊢
    simpa only [h] using hp
  rcases twoPoints L hinter ht hr hs hrs with h | h
  · exact lift r h h1
  · exact lift s h h2

lemma gateCases {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    (∃ a < N + i.val, (gs.get i).inputs = [a] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = V gs a x) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.and ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x && V gs b x)) ∨
    (∃ a < N + i.val, ∃ b < N + i.val, (gs.get i).op = GateOp.or ∧
      (gs.get i).inputs = [a, b] ∧
      ∀ x : Fin N → Bool, V gs (N + i.val) x = (V gs a x || V gs b x)) := by
  obtain ⟨hop, hlen⟩ := hG (gs.get i) (List.get_mem gs i)
  obtain ⟨hnon, earlier⟩ := htop i
  have val (x : Fin N → Bool) :
      V gs (N + i.val) x = (gs.get i).op.eval
        ((gs.get i).inputs.map fun r => if r < N + i.val then V gs r x else false) := by
    let D : Circuit := ⟨gs,0⟩
    have hw : N + i.val < N + D.size := Nat.add_lt_add_left i.isLt N
    have h := CoWire.gate_value D x (N + i.val) (by omega) hw
    simpa [D, CoWire.value, V, Circuit.eval, Circuit.wires] using h
  generalize eqg : gs.get i = g at hop hlen hnon earlier val ⊢
  cases ins : g.inputs with
  | nil => simp [ins] at hnon
  | cons a rest =>
    have ha : a < N + i.val := earlier a (by simp [ins])
    cases rest with
    | nil =>
      refine Or.inl ⟨a, ha, rfl, ?_⟩
      intro x
      rcases hop with hop | hop <;> simpa [ins, hop, GateOp.eval, ha] using val x
    | cons b rest =>
      cases rest with
      | nil =>
        have hb : b < N + i.val := earlier b (by simp [ins])
        rcases hop with hop | hop
        · refine Or.inr (Or.inl ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
        · refine Or.inr (Or.inr ⟨a, ha, b, hb, hop, rfl, ?_⟩)
          intro x
          simpa [ins, hop, GateOp.eval, ha, hb] using val x
      | cons c rest => simp [ins] at hlen

def Cond {N n : ℕ} (M : Finset (Fin N)) (a c : Fin n → Prop) (Sg : Fin n → Fin N → Prop)
    (j : ℕ) (X : Finset (Fin N)) : Prop :=
  ∀ i : Fin n, (i : ℕ) < j → a i → c i → ∀ s ∈ M, ∀ s' ∈ M, Sg i s → Sg i s' → (s ∈ X ↔ s' ∈ X)

def rel {N n : ℕ} (M : Finset (Fin N)) (a c : Fin n → Prop) (Sg : Fin n → Fin N → Prop)
    (j : ℕ) (r r' : Fin N) : Prop :=
  ∀ X : Finset (Fin N), Cond M a c Sg j X → (r ∈ X ↔ r' ∈ X)

def good {N n : ℕ} (M : Finset (Fin N)) (a c : Fin n → Prop) (Sg : Fin n → Fin N → Prop)
    (p0 p1 : Fin N) (hot : Fin n → Prop) (j : ℕ) (r : Fin N) : Prop :=
  ∀ x ∈ M, rel M a c Sg j r x →
    x ≠ p0 ∧ x ≠ p1 ∧ ∀ i : Fin n, (i : ℕ) < j → a i → c i → hot i → ¬ Sg i x

section relations
variable {N n : ℕ} {M : Finset (Fin N)} {a c : Fin n → Prop} {Sg : Fin n → Fin N → Prop}
  {p0 p1 : Fin N} {hot : Fin n → Prop}

lemma rel_refl (j : ℕ) (r : Fin N) : rel M a c Sg j r r := fun _ _ => Iff.rfl

lemma rel_symm {j : ℕ} {r t : Fin N} (h : rel M a c Sg j r t) : rel M a c Sg j t r :=
  fun X hX => (h X hX).symm

lemma rel_trans {j : ℕ} {r t u : Fin N} (h : rel M a c Sg j r t) (h' : rel M a c Sg j t u) :
    rel M a c Sg j r u := fun X hX => (h X hX).trans (h' X hX)

lemma rel_eqv {j : ℕ} {r t : Fin N} (h : rel M a c Sg j r t) (x : Fin N) :
    rel M a c Sg j r x ↔ rel M a c Sg j t x :=
  ⟨fun h' => rel_trans (rel_symm h) h', fun h' => rel_trans h h'⟩

lemma rel_mono {j j' : ℕ} (hj : j ≤ j') {r t : Fin N} (h : rel M a c Sg j r t) :
    rel M a c Sg j' r t := fun X hX => h X (fun i hi => hX i (lt_of_lt_of_le hi hj))

lemma rel_glue {j : ℕ} (i : Fin n) (hi : (i : ℕ) < j) (ha : a i) (hc : c i) {s s' : Fin N}
    (hs : s ∈ M) (hs' : s' ∈ M) (h : Sg i s) (h' : Sg i s') : rel M a c Sg j s s' :=
  fun X hX => hX i hi ha hc s hs s' hs' h h'

lemma rel_zero {r t : Fin N} (h : rel M a c Sg 0 r t) : r = t := by
  have h1 := (h {r} (fun i hi => absurd hi (Nat.not_lt_zero _))).mp (Finset.mem_singleton_self r)
  exact (Finset.mem_singleton.mp h1).symm

lemma rel_succ {j : ℕ} {r x : Fin N} (h : rel M a c Sg (j + 1) r x) (jj : Fin n)
    (hjj : (jj : ℕ) = j) :
    rel M a c Sg j r x ∨ ((∃ s ∈ M, Sg jj s ∧ rel M a c Sg j r s) ∧
      ∃ s' ∈ M, Sg jj s' ∧ rel M a c Sg j s' x) := by
  classical
  let P : Fin N → Prop := fun x => rel M a c Sg j r x ∨
    ((∃ s ∈ M, Sg jj s ∧ rel M a c Sg j r s) ∧ ∃ s' ∈ M, Sg jj s' ∧ rel M a c Sg j s' x)
  have aux : ∀ s ∈ M, ∀ s' ∈ M, Sg jj s → Sg jj s' → P s → P s' := by
    intro s hs s' hs' h1 h2 hp
    rcases hp with hp | hp
    · exact Or.inr ⟨⟨s, hs, h1, hp⟩, s', hs', h2, rel_refl _ _⟩
    · exact Or.inr ⟨hp.1, s', hs', h2, rel_refl _ _⟩
  have tr : ∀ s s', rel M a c Sg j s s' → P s → P s' := by
    intro s s' hss hp
    rcases hp with hp | ⟨hp1, s'', hs'', h2, h3⟩
    · exact Or.inl (rel_trans hp hss)
    · exact Or.inr ⟨hp1, s'', hs'', h2, rel_trans h3 hss⟩
  have mf : ∀ y, y ∈ Finset.univ.filter P ↔ P y := fun y => by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have cond : Cond M a c Sg (j + 1) (Finset.univ.filter P) := by
    intro i hi ha hc s hs s' hs' h1 h2
    rw [mf, mf]
    by_cases hlt : (i : ℕ) < j
    · have g : rel M a c Sg j s s' := rel_glue i hlt ha hc hs hs' h1 h2
      exact ⟨tr s s' g, tr s' s (rel_symm g)⟩
    · have hij : i = jj := Fin.ext (by omega)
      rw [hij] at h1 h2
      exact ⟨aux s hs s' hs' h1 h2, aux s' hs' s hs h2 h1⟩
  have key := h _ cond
  rw [mf, mf] at key
  exact key.mp (Or.inl (rel_refl _ _))

lemma good_back {j : ℕ} {r : Fin N} (h : good M a c Sg p0 p1 hot (j + 1) r) :
    good M a c Sg p0 p1 hot j r := by
  intro x hx hrx
  obtain ⟨h0, h1, h2⟩ := h x hx (rel_mono (Nat.le_succ j) hrx)
  exact ⟨h0, h1, fun i hi => h2 i (Nat.lt_succ_of_lt hi)⟩

lemma ub_char (M : Finset (Fin N)) (a c : Fin n → Prop) (Sg : Fin n → Fin N → Prop)
    (p0 p1 : Fin N) (hot : Fin n → Prop) (j : ℕ) (b : Finset (Fin N)) :
    ((∃ r ∈ M, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ M ∧ rel M a c Sg j r r')) ∧ p0 ∉ b ∧ p1 ∉ b ∧
      ∀ i : Fin n, (i : ℕ) < j → a i → c i → hot i → ∀ s ∈ b, ¬ Sg i s) ↔
    ∃ r ∈ M, good M a c Sg p0 p1 hot j r ∧ ∀ x, x ∈ b ↔ (x ∈ M ∧ rel M a c Sg j r x) := by
  constructor
  · rintro ⟨⟨r, hr, hb⟩, h0, h1, hh⟩
    refine ⟨r, hr, ?_, hb⟩
    intro x hx hrx
    have xb : x ∈ b := (hb x).mpr ⟨hx, hrx⟩
    refine ⟨fun e => h0 ?_, fun e => h1 ?_, fun i hi ha hc hh' => hh i hi ha hc hh' x xb⟩
    · rw [← e]; exact xb
    · rw [← e]; exact xb
  · rintro ⟨r, hr, hg, hb⟩
    refine ⟨⟨r, hr, hb⟩, ?_, ?_, ?_⟩
    · intro h
      have h' := (hb p0).mp h
      exact (hg p0 h'.1 h'.2).1 rfl
    · intro h
      have h' := (hb p1).mp h
      exact (hg p1 h'.1 h'.2).2.1 rfl
    · intro i hi ha hc hh s hs
      have h' := (hb s).mp hs
      exact (hg s h'.1 h'.2).2.2 i hi ha hc hh

lemma inactive (M : Finset (Fin N)) (a c : Fin n → Prop) (Sg : Fin n → Fin N → Prop)
    (p0 p1 : Fin N) (hot : Fin n → Prop) (jj : Fin n) (hna : ¬ (a jj ∧ c jj)) :
    (∀ r t, rel M a c Sg ((jj : ℕ) + 1) r t ↔ rel M a c Sg jj r t) ∧
    (∀ r, good M a c Sg p0 p1 hot ((jj : ℕ) + 1) r ↔ good M a c Sg p0 p1 hot jj r) := by
  have dead : ∀ i : Fin n, (i : ℕ) < (jj : ℕ) + 1 → ¬ (i : ℕ) < jj → a i → c i → False := by
    intro i hi hlt ha hc
    have hij : i = jj := Fin.ext (by omega)
    rw [hij] at ha hc
    exact hna ⟨ha, hc⟩
  have hrel : ∀ r t, rel M a c Sg ((jj : ℕ) + 1) r t ↔ rel M a c Sg jj r t := by
    intro r t
    constructor
    · intro h X hX
      refine h X (fun i hi ha hc => ?_)
      by_cases hlt : (i : ℕ) < jj
      · exact hX i hlt ha hc
      · exact (dead i hi hlt ha hc).elim
    · exact rel_mono (Nat.le_succ _)
  refine ⟨hrel, fun r => ⟨good_back, fun h x hx hrx => ?_⟩⟩
  obtain ⟨h0, h1, h2⟩ := h x hx ((hrel r x).mp hrx)
  refine ⟨h0, h1, fun i hi ha hc => ?_⟩
  by_cases hlt : (i : ℕ) < jj
  · exact h2 i hlt ha hc
  · exact (dead i hi hlt ha hc).elim

end relations

noncomputable def imgC {N : ℕ} (M : Finset (Fin N)) (F : Fin N → Fin N → Prop)
    (P : Fin N → Prop) : Finset (Finset (Fin N)) := by
  classical
  exact (M.filter P).image (fun r => M.filter (F r))

lemma mem_imgC {N : ℕ} {M : Finset (Fin N)} {F : Fin N → Fin N → Prop} {P : Fin N → Prop}
    {b : Finset (Fin N)} :
    b ∈ imgC M F P ↔ ∃ r ∈ M, P r ∧ ∀ x, x ∈ b ↔ (x ∈ M ∧ F r x) := by
  classical
  unfold imgC
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨r, ⟨hr, hp⟩, rfl⟩
    exact ⟨r, hr, hp, fun x => Finset.mem_filter⟩
  · rintro ⟨r, hr, hp, h⟩
    refine ⟨r, ⟨hr, hp⟩, ?_⟩
    ext x
    rw [h, Finset.mem_filter]

lemma imgC_pos {N : ℕ} {M : Finset (Fin N)} (F : Fin N → Fin N → Prop) (P : Fin N → Prop)
    (r : Fin N) (hr : r ∈ M) (hp : P r) : 1 ≤ (imgC M F P).card := by
  classical
  exact Finset.card_pos.mpr ⟨M.filter (F r), mem_imgC.mpr ⟨r, hr, hp, fun x => Finset.mem_filter⟩⟩

lemma imgC_one {N : ℕ} {M : Finset (Fin N)} (F : Fin N → Fin N → Prop) (P : Fin N → Prop)
    (eF : ∀ r t, F r t → ∀ x, (F r x ↔ F t x))
    (h : ∀ r ∈ M, ∀ t ∈ M, P r → P t → F r t) : (imgC M F P).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  obtain ⟨r, hr, hp, hx⟩ := mem_imgC.mp hb
  obtain ⟨t, ht, hp', hx'⟩ := mem_imgC.mp hb'
  ext x
  rw [hx, hx']
  exact and_congr_right fun _ => eF r t (h r hr t ht hp hp') x

theorem countStep {N : ℕ} (M : Finset (Fin N)) (E E' : Fin N → Fin N → Prop)
    (G G' mB : Fin N → Prop) (mT : Bool → Fin N → Prop) (U U' : Finset (Finset (Fin N)))
    (hU : ∀ b, b ∈ U ↔ ∃ r ∈ M, G r ∧ ∀ x, x ∈ b ↔ (x ∈ M ∧ E r x))
    (hU' : ∀ b, b ∈ U' ↔ ∃ r ∈ M, G' r ∧ ∀ x, x ∈ b ↔ (x ∈ M ∧ E' r x))
    (rE : ∀ r, E r r) (eE : ∀ r t, E r t → ∀ x, (E r x ↔ E t x))
    (rE' : ∀ r, E' r r) (eE' : ∀ r t, E' r t → ∀ x, (E' r x ↔ E' t x))
    (hBE : ∀ r t, mB r → E r t → mB t) (hBE' : ∀ r t, mB r → E' r t → mB t)
    (hN : ∀ r ∈ M, ¬ mB r → (G' r ↔ G r) ∧ ∀ t, (E' r t ↔ E r t))
    (hOne : ∀ r t, mB r → mB t → E' r t)
    (hGG : ∀ r, G' r → G r)
    (hTag : ∀ r, mB r → ∃ k, mT k r) (hT : ∀ k r t, mT k r → mT k t → E r t)
    (hC : ∀ r ∈ M, ∀ t ∈ M, G r → G t → mB r → mB t → ¬ E r t → G' r) :
    U'.card ≤ U.card ∧ U.card ≤ U'.card + 1 ∧
      ((∀ r ∈ M, ∀ t ∈ M, G r → G t → mB r → mB t → E r t) →
        (∀ r ∈ M, G r → mB r → G' r) → U.card = U'.card) := by
  classical
  have hUW : U = imgC M E (fun r => G r ∧ ¬ mB r) ∪ imgC M E (fun r => G r ∧ mB r) := by
    ext b
    rw [hU, Finset.mem_union, mem_imgC, mem_imgC]
    constructor
    · rintro ⟨r, hr, hg, hb⟩
      by_cases hm : mB r
      · exact Or.inr ⟨r, hr, ⟨hg, hm⟩, hb⟩
      · exact Or.inl ⟨r, hr, ⟨hg, hm⟩, hb⟩
    · rintro (⟨r, hr, ⟨hg, _⟩, hb⟩ | ⟨r, hr, ⟨hg, _⟩, hb⟩)
      · exact ⟨r, hr, hg, hb⟩
      · exact ⟨r, hr, hg, hb⟩
  have hUW' : U' = imgC M E (fun r => G r ∧ ¬ mB r) ∪ imgC M E' (fun r => G' r ∧ mB r) := by
    ext b
    rw [hU', Finset.mem_union, mem_imgC, mem_imgC]
    constructor
    · rintro ⟨r, hr, hg, hb⟩
      by_cases hm : mB r
      · exact Or.inr ⟨r, hr, ⟨hg, hm⟩, hb⟩
      · exact Or.inl ⟨r, hr, ⟨(hN r hr hm).1.mp hg, hm⟩,
          fun x => (hb x).trans (and_congr_right fun _ => (hN r hr hm).2 x)⟩
    · rintro (⟨r, hr, ⟨hg, hm⟩, hb⟩ | ⟨r, hr, ⟨hg, _⟩, hb⟩)
      · exact ⟨r, hr, (hN r hr hm).1.mpr hg,
          fun x => (hb x).trans (and_congr_right fun _ => ((hN r hr hm).2 x).symm)⟩
      · exact ⟨r, hr, hg, hb⟩
  have dWV : Disjoint (imgC M E (fun r => G r ∧ ¬ mB r)) (imgC M E (fun r => G r ∧ mB r)) := by
    rw [Finset.disjoint_left]
    intro b hbW hbV
    obtain ⟨r, hr, ⟨_, hnm⟩, hb⟩ := mem_imgC.mp hbW
    obtain ⟨t, ht, ⟨_, hm⟩, hb'⟩ := mem_imgC.mp hbV
    have hrb : r ∈ b := (hb r).mpr ⟨hr, rE r⟩
    exact hnm (hBE t r hm ((hb' r).mp hrb).2)
  have dWV' : Disjoint (imgC M E (fun r => G r ∧ ¬ mB r))
      (imgC M E' (fun r => G' r ∧ mB r)) := by
    rw [Finset.disjoint_left]
    intro b hbW hbV
    obtain ⟨r, hr, ⟨_, hnm⟩, hb⟩ := mem_imgC.mp hbW
    obtain ⟨t, ht, ⟨_, hm⟩, hb'⟩ := mem_imgC.mp hbV
    have hrb : r ∈ b := (hb r).mpr ⟨hr, rE r⟩
    exact hnm (hBE' t r hm ((hb' r).mp hrb).2)
  have cU := Finset.card_union_of_disjoint dWV
  have cU' := Finset.card_union_of_disjoint dWV'
  rw [← hUW] at cU
  rw [← hUW'] at cU'
  have v1 : (imgC M E' (fun r => G' r ∧ mB r)).card ≤ 1 :=
    imgC_one E' _ eE' (fun r _ t _ hp hp' => hOne r t hp.2 hp'.2)
  have vk : ∀ k, (imgC M E (fun r => G r ∧ mT k r)).card ≤ 1 := fun k =>
    imgC_one E _ eE (fun r _ t _ hp hp' => hT k r t hp.2 hp'.2)
  have v2 : (imgC M E (fun r => G r ∧ mB r)).card ≤ 2 := by
    have hsub : imgC M E (fun r => G r ∧ mB r) ⊆
        imgC M E (fun r => G r ∧ mT true r) ∪ imgC M E (fun r => G r ∧ mT false r) := by
      intro b hb
      obtain ⟨r, hr, ⟨hg, hm⟩, hx⟩ := mem_imgC.mp hb
      obtain ⟨k, hk⟩ := hTag r hm
      cases k
      · exact Finset.mem_union.mpr (Or.inr (mem_imgC.mpr ⟨r, hr, ⟨hg, hk⟩, hx⟩))
      · exact Finset.mem_union.mpr (Or.inl (mem_imgC.mpr ⟨r, hr, ⟨hg, hk⟩, hx⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (imgC M E (fun r => G r ∧ mT true r))
      (imgC M E (fun r => G r ∧ mT false r))
    have h3 := vk true
    have h4 := vk false
    omega
  have vI : (imgC M E' (fun r => G' r ∧ mB r)).card ≤ (imgC M E (fun r => G r ∧ mB r)).card := by
    by_cases hne : (imgC M E' (fun r => G' r ∧ mB r)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨r, hr, ⟨hg, hm⟩, _⟩ := mem_imgC.mp hb
      have := imgC_pos E (fun r => G r ∧ mB r) r hr ⟨hGG r hg, hm⟩
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have vII : (imgC M E (fun r => G r ∧ mB r)).card ≤
      (imgC M E' (fun r => G' r ∧ mB r)).card + 1 := by
    by_cases h : 1 ≤ (imgC M E' (fun r => G' r ∧ mB r)).card
    · omega
    · have : (imgC M E (fun r => G r ∧ mB r)).card ≤ 1 := by
        apply imgC_one E _ eE
        intro r hr t ht hp hp'
        by_contra hnE
        have hg' := hC r hr t ht hp.1 hp'.1 hp.2 hp'.2 hnE
        exact h (imgC_pos E' (fun r => G' r ∧ mB r) r hr ⟨hg', hp.2⟩)
      omega
  refine ⟨by omega, by omega, fun l1 l2 => ?_⟩
  have w1 : (imgC M E (fun r => G r ∧ mB r)).card ≤ 1 :=
    imgC_one E _ eE (fun r hr t ht hp hp' => l1 r hr t ht hp.1 hp'.1 hp.2 hp'.2)
  have w2 : (imgC M E (fun r => G r ∧ mB r)).card ≤ (imgC M E' (fun r => G' r ∧ mB r)).card := by
    by_cases hne : (imgC M E (fun r => G r ∧ mB r)).Nonempty
    · obtain ⟨b, hb⟩ := hne
      obtain ⟨r, hr, ⟨hg, hm⟩, _⟩ := mem_imgC.mp hb
      have := imgC_pos E' (fun r => G' r ∧ mB r) r hr ⟨l2 r hr hg hm, hm⟩
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  omega

theorem activeStep {N n : ℕ} (M : Finset (Fin N)) (a c : Fin n → Prop)
    (Sg : Fin n → Fin N → Prop) (p0 p1 : Fin N) (hot : Fin n → Prop) (jj : Fin n)
    (ha : a jj) (hc : c jj) (Tg : Bool → Fin N → Prop) (hotIn : Bool → Prop) (Q : Prop)
    (U U' : Finset (Finset (Fin N)))
    (hU : ∀ b, b ∈ U ↔ ∃ r ∈ M, good M a c Sg p0 p1 hot jj r ∧
      ∀ x, x ∈ b ↔ (x ∈ M ∧ rel M a c Sg jj r x))
    (hU' : ∀ b, b ∈ U' ↔ ∃ r ∈ M, good M a c Sg p0 p1 hot ((jj : ℕ) + 1) r ∧
      ∀ x, x ∈ b ↔ (x ∈ M ∧ rel M a c Sg ((jj : ℕ) + 1) r x))
    (S1 : ∀ s, Sg jj s ↔ ∃ k, Tg k s)
    (S2 : ∀ k, ∀ s ∈ M, ∀ s' ∈ M, Tg k s → Tg k s' → rel M a c Sg jj s s')
    (S3 : ∀ k, ∀ t ∈ M, good M a c Sg p0 p1 hot jj t → ∀ s ∈ M, Tg k s →
      rel M a c Sg jj t s → ¬ hotIn k)
    (S3' : hot jj → ∃ k, hotIn k)
    (S4a : ∀ s ∈ M, ∀ s' ∈ M, s ≠ s' → Sg jj s → Sg jj s' → (∃ k, ¬ hotIn k) → Q)
    (S4b : hot jj → ∀ s ∈ M, s ≠ p0 → s ≠ p1 → Sg jj s → (∃ k, ¬ hotIn k) → Q) :
    U'.card ≤ U.card ∧ U.card ≤ U'.card + 1 ∧ (¬ Q → U.card = U'.card) := by
  have cover : ∀ k1 k2 : Bool, k1 ≠ k2 → ∀ k, k = k1 ∨ k = k2 := by decide
  have sc : ∀ r x, rel M a c Sg ((jj : ℕ) + 1) r x → rel M a c Sg jj r x ∨
      ((∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) ∧ ∃ s' ∈ M, Sg jj s' ∧ rel M a c Sg jj s' x) :=
    fun r x h => rel_succ h jj rfl
  have up : ∀ r t, rel M a c Sg jj r t → rel M a c Sg ((jj : ℕ) + 1) r t :=
    fun r t h => rel_mono (Nat.le_succ _) h
  have last : ∀ i : Fin n, (i : ℕ) < (jj : ℕ) + 1 → ¬ (i : ℕ) < jj → i = jj :=
    fun i hi hlt => Fin.ext (by omega)
  have hBE : ∀ r t, (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) → rel M a c Sg jj r t →
      ∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj t s := by
    rintro r t ⟨s, hs, hS, hrs⟩ hrt
    exact ⟨s, hs, hS, rel_trans (rel_symm hrt) hrs⟩
  have hBE' : ∀ r t, (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) →
      rel M a c Sg ((jj : ℕ) + 1) r t → ∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj t s := by
    intro r t hm h
    rcases sc r t h with h | ⟨_, s', hs', hS', h'⟩
    · exact hBE r t hm h
    · exact ⟨s', hs', hS', rel_symm h'⟩
  have hN : ∀ r ∈ M, ¬ (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) →
      (good M a c Sg p0 p1 hot ((jj : ℕ) + 1) r ↔ good M a c Sg p0 p1 hot jj r) ∧
      ∀ t, (rel M a c Sg ((jj : ℕ) + 1) r t ↔ rel M a c Sg jj r t) := by
    intro r hr hm
    have down : ∀ t, rel M a c Sg ((jj : ℕ) + 1) r t → rel M a c Sg jj r t :=
      fun t h => (sc r t h).resolve_right (fun h' => hm h'.1)
    refine ⟨⟨good_back, fun hg x hx hrx => ?_⟩, fun t => ⟨down t, up r t⟩⟩
    have hrx' := down x hrx
    obtain ⟨h0, h1, h2⟩ := hg x hx hrx'
    refine ⟨h0, h1, fun i hi hai hci hh hS => ?_⟩
    by_cases hlt : (i : ℕ) < jj
    · exact h2 i hlt hai hci hh hS
    · rw [last i hi hlt] at hS
      exact hm ⟨x, hx, hS, hrx'⟩
  have hOne : ∀ r t, (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) →
      (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj t s) → rel M a c Sg ((jj : ℕ) + 1) r t := by
    rintro r t ⟨s, hs, hS, hrs⟩ ⟨s', hs', hS', hts'⟩
    exact rel_trans (up _ _ hrs) (rel_trans
      (rel_glue jj (Nat.lt_succ_self _) ha hc hs hs' hS hS') (rel_symm (up _ _ hts')))
  have hTag : ∀ r, (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) →
      ∃ k, ∃ s ∈ M, Tg k s ∧ rel M a c Sg jj r s := by
    rintro r ⟨s, hs, hS, hrs⟩
    obtain ⟨k, hk⟩ := (S1 s).mp hS
    exact ⟨k, s, hs, hk, hrs⟩
  have hT : ∀ k r t, (∃ s ∈ M, Tg k s ∧ rel M a c Sg jj r s) →
      (∃ s ∈ M, Tg k s ∧ rel M a c Sg jj t s) → rel M a c Sg jj r t := by
    rintro k r t ⟨s, hs, hS, hrs⟩ ⟨s', hs', hS', hts'⟩
    exact rel_trans hrs (rel_trans (S2 k s hs s' hs' hS hS') (rel_symm hts'))
  have hC : ∀ r ∈ M, ∀ t ∈ M, good M a c Sg p0 p1 hot jj r → good M a c Sg p0 p1 hot jj t →
      (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s) → (∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj t s) →
      ¬ rel M a c Sg jj r t → good M a c Sg p0 p1 hot ((jj : ℕ) + 1) r := by
    rintro r hr t ht hg hg' ⟨s1, hs1, hS1, hrs1⟩ ⟨s2, hs2, hS2, hts2⟩ hnE
    obtain ⟨k1, hk1⟩ := (S1 s1).mp hS1
    obtain ⟨k2, hk2⟩ := (S1 s2).mp hS2
    have hne : k1 ≠ k2 := by
      intro e
      rw [e] at hk1
      exact hnE (rel_trans hrs1 (rel_trans (S2 k2 s1 hs1 s2 hs2 hk1 hk2) (rel_symm hts2)))
    have nh1 : ¬ hotIn k1 := S3 k1 r hr hg s1 hs1 hk1 hrs1
    have nh2 : ¬ hotIn k2 := S3 k2 t ht hg' s2 hs2 hk2 hts2
    have near : ∀ s' ∈ M, Sg jj s' → rel M a c Sg jj r s' ∨ rel M a c Sg jj t s' := by
      intro s' hs' hS'
      obtain ⟨k, hk⟩ := (S1 s').mp hS'
      rcases cover k1 k2 hne k with e | e
      · rw [e] at hk
        exact Or.inl (rel_trans hrs1 (S2 k1 s1 hs1 s' hs' hk1 hk))
      · rw [e] at hk
        exact Or.inr (rel_trans hts2 (S2 k2 s2 hs2 s' hs' hk2 hk))
    intro x hx hrx
    have cls : rel M a c Sg jj r x ∨ rel M a c Sg jj t x := by
      rcases sc r x hrx with h | ⟨_, s', hs', hS', h'⟩
      · exact Or.inl h
      · rcases near s' hs' hS' with h | h
        · exact Or.inl (rel_trans h h')
        · exact Or.inr (rel_trans h h')
    have b3 := cls.elim (hg x hx) (hg' x hx)
    refine ⟨b3.1, b3.2.1, fun i hi hai hci hh => ?_⟩
    by_cases hlt : (i : ℕ) < jj
    · exact b3.2.2 i hlt hai hci hh
    · rw [last i hi hlt] at hh
      obtain ⟨k, hk⟩ := S3' hh
      rcases cover k1 k2 hne k with e | e
      · rw [e] at hk
        exact absurd hk nh1
      · rw [e] at hk
        exact absurd hk nh2
  obtain ⟨r1, r2, r3⟩ := countStep M (rel M a c Sg jj) (rel M a c Sg ((jj : ℕ) + 1))
    (good M a c Sg p0 p1 hot jj) (good M a c Sg p0 p1 hot ((jj : ℕ) + 1))
    (fun r => ∃ s ∈ M, Sg jj s ∧ rel M a c Sg jj r s)
    (fun k r => ∃ s ∈ M, Tg k s ∧ rel M a c Sg jj r s) U U' hU hU'
    (fun r => rel_refl _ r) (fun r t h x => rel_eqv h x)
    (fun r => rel_refl _ r) (fun r t h x => rel_eqv h x)
    hBE hBE' hN hOne (fun r => good_back) hTag hT hC
  refine ⟨r1, r2, fun hQ => r3 ?_ ?_⟩
  · rintro r hr t ht hg hg' ⟨s1, hs1, hS1, hrs1⟩ ⟨s2, hs2, hS2, hts2⟩
    by_contra hnE
    obtain ⟨k1, hk1⟩ := (S1 s1).mp hS1
    have hne : s1 ≠ s2 := by
      intro e
      rw [e] at hrs1
      exact hnE (rel_trans hrs1 (rel_symm hts2))
    exact hQ (S4a s1 hs1 s2 hs2 hne hS1 hS2 ⟨k1, S3 k1 r hr hg s1 hs1 hk1 hrs1⟩)
  · rintro r hr hg ⟨s1, hs1, hS1, hrs1⟩
    obtain ⟨k1, hk1⟩ := (S1 s1).mp hS1
    have nh1 : ¬ hotIn k1 := S3 k1 r hr hg s1 hs1 hk1 hrs1
    intro x hx hrx
    have hrx' : rel M a c Sg jj r x := by
      rcases sc r x hrx with h | ⟨_, s', hs', hS', h'⟩
      · exact h
      · by_cases e : s1 = s'
        · rw [← e] at h'
          exact rel_trans hrs1 h'
        · exact absurd (S4a s1 hs1 s' hs' e hS1 hS' ⟨k1, nh1⟩) hQ
    obtain ⟨h0, h1, h2⟩ := hg x hx hrx'
    refine ⟨h0, h1, fun i hi hai hci hh => ?_⟩
    by_cases hlt : (i : ℕ) < jj
    · exact h2 i hlt hai hci hh
    · rw [last i hi hlt] at hh
      have g1 := hg s1 hs1 hrs1
      exact absurd (S4b hh s1 hs1 g1.1 g1.2.1 hS1 ⟨k1, nh1⟩) hQ

lemma gateEnum {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length) :
    ∃ e : Bool → ℕ, (∀ k, e k ∈ (gs.get i).inputs) ∧ ∀ w ∈ (gs.get i).inputs, ∃ k, e k = w := by
  rcases gateCases gs hG htop i with
    ⟨a, _, hin, _⟩ | ⟨a, _, b, _, _, hin, _⟩ | ⟨a, _, b, _, _, hin, _⟩
  · refine ⟨fun _ => a, fun _ => by rw [hin]; simp, fun w hw => ⟨true, ?_⟩⟩
    rw [hin] at hw
    exact (List.mem_singleton.mp hw).symm
  · refine ⟨fun k => cond k a b, fun k => by rw [hin]; cases k <;> simp, fun w hw => ?_⟩
    rw [hin] at hw
    have hw' : w = a ∨ w = b := by simpa using hw
    rcases hw' with h | h
    · exact ⟨true, h.symm⟩
    · exact ⟨false, h.symm⟩
  · refine ⟨fun k => cond k a b, fun k => by rw [hin]; cases k <;> simp, fun w hw => ?_⟩
    rw [hin] at hw
    have hw' : w = a ∨ w = b := by simpa using hw
    rcases hw' with h | h
    · exact ⟨true, h.symm⟩
    · exact ⟨false, h.symm⟩

lemma orIn {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length)
    (hor : (gs.get i).op = GateOp.or) (e : ℕ) (he : e ∈ (gs.get i).inputs)
    (x : Fin N → Bool) (hx : V gs e x = true) : V gs (N + i.val) x = true := by
  rcases gateCases gs hG htop i with
    ⟨a, _, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩ | ⟨a, _, b, _, _, hin, heq⟩
  · rw [hin] at he
    have hea : e = a := List.mem_singleton.mp he
    rw [hea] at hx
    exact (heq x).trans hx
  · rw [hor] at hop
    cases hop
  · rw [hin] at he
    have hea : e = a ∨ e = b := by simpa using he
    refine (heq x).trans ?_
    rcases hea with h | h
    · rw [h] at hx
      rw [hx]
      rfl
    · rw [h] at hx
      rw [hx]
      exact Bool.or_true _

lemma orOut {N : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val) (i : Fin gs.length)
    (hor : (gs.get i).op = GateOp.or)
    (x : Fin N → Bool) (hx : V gs (N + i.val) x = true) :
    ∃ e ∈ (gs.get i).inputs, V gs e x = true := by
  rcases gateCases gs hG htop i with
    ⟨a, _, hin, heq⟩ | ⟨a, _, b, _, hop, _, _⟩ | ⟨a, _, b, _, _, hin, heq⟩
  · exact ⟨a, by rw [hin]; simp, (heq x).symm.trans hx⟩
  · rw [hor] at hop
    cases hop
  · have h := (heq x).symm.trans hx
    have h' : V gs a x = true ∨ V gs b x = true := by
      simpa only [Bool.or_eq_true] using h
    rcases h' with h1 | h1
    · exact ⟨a, by rw [hin]; simp, h1⟩
    · exact ⟨b, by rw [hin]; simp, h1⟩

def Closed (N : ℕ) (gs : List Gate) (Zs : Set ℕ) : Prop :=
  ∀ k : Fin gs.length, N + (k : ℕ) ∈ Zs → (gs.get k).op = GateOp.or →
    ∀ e ∈ (gs.get k).inputs, e ∈ Zs

section reach
variable {N : ℕ} {gs : List Gate} {St : ℕ → Fin N → Prop}

lemma stIn (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
    (p : ℕ) ∈ Zs) (w : ℕ) (hw : w < N) (p : Fin N) (h : St w p) : w = (p : ℕ) := by
  have h1 : (p : ℕ) ∈ ({w} : Set ℕ) := (hSt w p).mp h {w} rfl (by
    intro k hk
    have hk' : N + (k : ℕ) = w := hk
    omega)
  exact (Set.mem_singleton_iff.mp h1).symm

lemma stAnd (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
    (p : ℕ) ∈ Zs) (k : Fin gs.length) (hand : (gs.get k).op = GateOp.and) (p : Fin N)
    (h : St (N + (k : ℕ)) p) : False := by
  have h1 : (p : ℕ) ∈ ({N + (k : ℕ)} : Set ℕ) := (hSt _ p).mp h {N + (k : ℕ)} rfl (by
    intro k' hk' hor
    have hk'' : N + (k' : ℕ) = N + (k : ℕ) := hk'
    have hkk : k' = k := Fin.ext (by omega)
    rw [hkk, hand] at hor
    cases hor)
  have h2 : (p : ℕ) = N + (k : ℕ) := h1
  have := p.isLt
  omega

lemma stOrUp (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
    (p : ℕ) ∈ Zs) (k : Fin gs.length) (hor : (gs.get k).op = GateOp.or) (e : ℕ)
    (he : e ∈ (gs.get k).inputs) (p : Fin N) (h : St e p) : St (N + (k : ℕ)) p := by
  rw [hSt] at h ⊢
  intro Zs hz hcl
  exact h Zs (hcl k hz hor e he) hcl

lemma stOrDown (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
    (p : ℕ) ∈ Zs) (k : Fin gs.length) (p : Fin N)
    (h : St (N + (k : ℕ)) p) : ∃ e ∈ (gs.get k).inputs, St e p := by
  have cl : Closed N gs (setOf fun u => u = N + (k : ℕ) ∨ ∃ e ∈ (gs.get k).inputs,
      ∀ Z : Set ℕ, e ∈ Z → Closed N gs Z → u ∈ Z) := by
    intro k' hk' hor' e' he'
    have hk'' : N + (k' : ℕ) = N + (k : ℕ) ∨ ∃ e ∈ (gs.get k).inputs,
      ∀ Z : Set ℕ, e ∈ Z → Closed N gs Z → N + (k' : ℕ) ∈ Z := hk'
    show e' = N + (k : ℕ) ∨ ∃ e ∈ (gs.get k).inputs,
      ∀ Z : Set ℕ, e ∈ Z → Closed N gs Z → e' ∈ Z
    rcases hk'' with h1 | ⟨e, he, h2⟩
    · have hkk : k' = k := Fin.ext (by omega)
      rw [hkk] at he'
      exact Or.inr ⟨e', he', fun Z hZ _ => hZ⟩
    · exact Or.inr ⟨e, he, fun Z hZ hcl => hcl k' (h2 Z hZ hcl) hor' e' he'⟩
  have h1 : (p : ℕ) = N + (k : ℕ) ∨ ∃ e ∈ (gs.get k).inputs,
      ∀ Z : Set ℕ, e ∈ Z → Closed N gs Z → (p : ℕ) ∈ Z :=
    (hSt _ p).mp h _ (Or.inl rfl) cl
  rcases h1 with h1 | ⟨e, he, h2⟩
  · have := p.isLt
    omega
  · exact ⟨e, he, (hSt e p).mpr h2⟩

lemma stTrue (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val)
    (hSt : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
    (p : ℕ) ∈ Zs) (w : ℕ) (p : Fin N) (h : St w p) (x : Fin N → Bool) (hx : x p = true) :
    V gs w x = true := by
  cases hv : V gs w x with
  | true => rfl
  | false =>
    have h1 : V gs (p : ℕ) x = false := (hSt w p).mp h (setOf fun u => V gs u x = false) hv (by
      intro k hk hor e he
      have hk' : V gs (N + (k : ℕ)) x = false := hk
      show V gs e x = false
      cases he' : V gs e x with
      | false => rfl
      | true => exact absurd ((orIn gs hG htop k hor e he x he').symm.trans hk') (by decide))
    have h2 : V gs (p : ℕ) x = x p := CoWire.input_value ⟨gs, (p : ℕ)⟩ x p
    rw [h2, hx] at h1
    cases h1

end reach

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card := by
  classical
  intro q N L i0 p0 p1 _hq _hN hsize hinter _hpair hne hp0 hp1 gs hG hlen hlt ev hev o0 _hbase
    _h0 _h1 _hrim St hSt UB hUB Xs hXs
  have htop : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < N + i.val := fun i => ⟨hlen i, hlt i⟩
  have m0 : p0 ∈ ({p0, p1} : Finset (Fin N)) := Finset.mem_insert_self _ _
  have m1 : p1 ∈ ({p0, p1} : Finset (Fin N)) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hTsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hp0
    · rw [Finset.mem_singleton.mp h]; exact hp1
  have hSt' : ∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → Closed N gs Zs →
      (p : ℕ) ∈ Zs := hSt
  let a : Fin gs.length → Prop := fun i => (gs.get i).op = GateOp.or
  let c : Fin gs.length → Prop := fun i =>
    ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false
  let Sg : Fin gs.length → Fin N → Prop := fun i s => St (N + (i : ℕ)) s
  let hot : Fin gs.length → Prop := fun i =>
    ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
      ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true
  have hUB' : ∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔
      ∃ r ∈ L i0, good (L i0) a c Sg p0 p1 hot j r ∧
        ∀ x, x ∈ b ↔ (x ∈ L i0 ∧ rel (L i0) a c Sg j r x) :=
    fun j b => (hUB j b).trans (ub_char (L i0) a c Sg p0 p1 hot j b)
  have stEv : ∀ (w : ℕ) (s : Fin N), St w s → ev w (fun v : Fin N => decide (v = s)) = true :=
    fun w s h => (hev _ _).trans (stTrue hG htop hSt' w s h _ (decide_eq_true rfl))
  have stepJ : ∀ j : Fin gs.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧
      (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
      (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card) := by
    intro j
    by_cases hact : a j ∧ c j
    · obtain ⟨hor, hcold⟩ := hact
      have hor' : (gs.get j).op = GateOp.or := hor
      have hcold' : ev (N + (j : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false := hcold
      have hcoldV : V gs (N + j.val) (base (L i0)) = false := (hev _ _).symm.trans hcold'
      obtain ⟨e, he_mem, he_surj⟩ := gateEnum gs hG htop j
      have coldE : ∀ k, V gs (e k) (base (L i0)) = false := by
        intro k
        cases hv : V gs (e k) (base (L i0)) with
        | false => rfl
        | true =>
          exact absurd ((orIn gs hG htop j hor' (e k) (he_mem k) _ hv).symm.trans hcoldV)
            (by decide)
      have wcase : ∀ k, e k < N ∨ ∃ i : Fin gs.length, e k = N + i.val ∧ i.val < j.val := by
        intro k
        have h1 := hlt j (e k) (he_mem k)
        by_cases h : e k < N
        · exact Or.inl h
        · have hj := j.isLt
          refine Or.inr ⟨⟨e k - N, by omega⟩, ?_, ?_⟩
          · show e k = N + (e k - N)
            omega
          · show e k - N < j.val
            omega
      have gcase : ∀ k (i : Fin gs.length), e k = N + i.val → (gs.get i).op = GateOp.or →
          c i := by
        intro k i hi _
        have h1 := coldE k
        rw [hi] at h1
        exact (hev _ _).trans h1
      have toXs : ∀ s ∈ L i0, ∀ s' ∈ L i0, s ≠ s' →
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v = s)) = true →
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v = s')) = true →
          (∃ k, ¬ (ev (e k) (fun v : Fin N => decide (v = p0)) = true ∨
            ev (e k) (fun v : Fin N => decide (v = p1)) = true)) → j ∈ Xs := by
        rintro s hs s' hs' hne' h h' ⟨k, hk⟩
        rw [hXs]
        refine ⟨hor', hcold', fun t ht => ?_, fun hall => hk (hall (e k) (he_mem k))⟩
        exact (hev _ _).trans (offOther gs (N + j.val) L hG hinter hs hs' hne'
          ((hev _ _).symm.trans h) ((hev _ _).symm.trans h') t ht)
      refine activeStep (L i0) a c Sg p0 p1 hot j hor hcold (fun k s => St (e k) s)
        (fun k => ev (e k) (fun v : Fin N => decide (v = p0)) = true ∨
          ev (e k) (fun v : Fin N => decide (v = p1)) = true) (j ∈ Xs)
        (UB j) (UB ((j : ℕ) + 1)) (hUB' j) (hUB' ((j : ℕ) + 1)) ?_ ?_ ?_ ?_ ?_ ?_
      · intro s
        constructor
        · intro h
          obtain ⟨w, hw, hws⟩ := stOrDown hSt' j s h
          obtain ⟨k, hk⟩ := he_surj w hw
          rw [← hk] at hws
          exact ⟨k, hws⟩
        · rintro ⟨k, hk⟩
          exact stOrUp hSt' j hor' (e k) (he_mem k) s hk
      · intro k s hs s' hs' h h'
        have h2 : St (e k) s := h
        have h2' : St (e k) s' := h'
        rcases wcase k with hin | ⟨i, hi, hij⟩
        · have e1 := stIn hSt' (e k) hin s h2
          have e2 := stIn hSt' (e k) hin s' h2'
          have hss : s = s' := Fin.ext (e1.symm.trans e2)
          rw [hss]
          exact rel_refl _ _
        · rw [hi] at h2 h2'
          rcases (hG (gs.get i) (List.get_mem gs i)).1 with hand | hori
          · exact (stAnd hSt' i hand s h2).elim
          · exact rel_glue i hij hori (gcase k i hi hori) hs hs' h2 h2'
      · intro k t ht hg s hs hk hts hhot
        have hk2 : St (e k) s := hk
        obtain ⟨g0, g1, g2⟩ := hg s hs hts
        rcases wcase k with hin | ⟨i, hi, hij⟩
        · have e1 := stIn hSt' (e k) hin s hk2
          have evin : ∀ x : Fin N → Bool, ev (e k) x = x s := by
            intro x
            rw [hev, e1]
            exact CoWire.input_value ⟨gs, (s : ℕ)⟩ x s
          rcases hhot with h | h
          · rw [evin] at h
            exact g0 (of_decide_eq_true h)
          · rw [evin] at h
            exact g1 (of_decide_eq_true h)
        · rw [hi] at hk2 hhot
          rcases (hG (gs.get i) (List.get_mem gs i)).1 with hand | hori
          · exact stAnd hSt' i hand s hk2
          · exact g2 i hij hori (gcase k i hi hori) hhot hk2
      · intro hh
        have hh' : ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = true := hh
        rcases hh' with h | h
        · obtain ⟨w, hw, hwv⟩ := orOut gs hG htop j hor' _ ((hev _ _).symm.trans h)
          obtain ⟨k, hk⟩ := he_surj w hw
          rw [← hk] at hwv
          exact ⟨k, Or.inl ((hev _ _).trans hwv)⟩
        · obtain ⟨w, hw, hwv⟩ := orOut gs hG htop j hor' _ ((hev _ _).symm.trans h)
          obtain ⟨k, hk⟩ := he_surj w hw
          rw [← hk] at hwv
          exact ⟨k, Or.inr ((hev _ _).trans hwv)⟩
      · intro s hs s' hs' hne' h h' hk
        exact toXs s hs s' hs' hne' (stEv _ s h) (stEv _ s' h') hk
      · intro hh s hs hs0 hs1 h hk
        have hh' : ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨
          ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = true := hh
        rcases hh' with h0 | h1
        · exact toXs p0 hp0 s hs (Ne.symm hs0) h0 (stEv _ s h) hk
        · exact toXs p1 hp1 s hs (Ne.symm hs1) h1 (stEv _ s h) hk
    · obtain ⟨hrel, hgood⟩ := inactive (L i0) a c Sg p0 p1 hot j hact
      have heq : UB ((j : ℕ) + 1) = UB j := by
        ext b
        rw [hUB', hUB']
        constructor
        · rintro ⟨r, hr, hg, hb⟩
          exact ⟨r, hr, (hgood r).mp hg,
            fun x => (hb x).trans (and_congr_right fun _ => hrel r x)⟩
        · rintro ⟨r, hr, hg, hb⟩
          exact ⟨r, hr, (hgood r).mpr hg,
            fun x => (hb x).trans (and_congr_right fun _ => (hrel r x).symm)⟩
      rw [heq]
      exact ⟨le_rfl, Nat.le_succ _, fun _ => rfl⟩
  have h0card : (UB 0).card = q - 1 := by
    have himg : UB 0 = (L i0 \ {p0, p1}).image (fun r => ({r} : Finset (Fin N))) := by
      ext b
      rw [hUB', Finset.mem_image]
      constructor
      · rintro ⟨r, hr, hg, hb⟩
        have g := hg r hr (rel_refl _ _)
        refine ⟨r, Finset.mem_sdiff.mpr ⟨hr, ?_⟩, ?_⟩
        · intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact g.1 h
          · exact g.2.1 (Finset.mem_singleton.mp h)
        · ext x
          rw [hb, Finset.mem_singleton]
          constructor
          · intro hx
            rw [hx]
            exact ⟨hr, rel_refl _ _⟩
          · rintro ⟨_, hrel⟩
            exact (rel_zero hrel).symm
      · rintro ⟨r, hr, hbr⟩
        obtain ⟨hrM, hrT⟩ := Finset.mem_sdiff.mp hr
        refine ⟨r, hrM, ?_, fun x => ?_⟩
        · intro x hx hrx
          have hx' : x = r := (rel_zero hrx).symm
          rw [hx']
          exact ⟨fun e => hrT (by rw [e]; exact m0), fun e => hrT (by rw [e]; exact m1),
            fun i hi => absurd hi (Nat.not_lt_zero _)⟩
        · rw [← hbr, Finset.mem_singleton]
          constructor
          · intro hx
            rw [hx]
            exact ⟨hrM, rel_refl _ _⟩
          · rintro ⟨_, h⟩
            exact (rel_zero h).symm
    rw [himg, Finset.card_image_of_injective _ Finset.singleton_injective,
      Finset.card_sdiff_of_subset hTsub, hsize, Finset.card_pair hne]
    omega
  have tele : ∀ k, k ≤ gs.length →
      (UB 0).card ≤ (UB k).card + (Xs.filter (fun i => i.val < k)).card := by
    intro k
    induction k with
    | zero =>
      intro _
      omega
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨_, s2, s3⟩ := stepJ ⟨k, by omega⟩
      have s2' : (UB k).card ≤ (UB (k + 1)).card + 1 := s2
      by_cases hin : (⟨k, by omega⟩ : Fin gs.length) ∈ Xs
      · have hnot : (⟨k, by omega⟩ : Fin gs.length) ∉ Xs.filter (fun i => i.val < k) :=
          fun h => Nat.lt_irrefl k (Finset.mem_filter.mp h).2
        have hsub : insert (⟨k, by omega⟩ : Fin gs.length) (Xs.filter (fun i => i.val < k)) ⊆
            Xs.filter (fun i => i.val < k + 1) := by
          intro i hi
          rcases Finset.mem_insert.mp hi with h | h
          · rw [h]
            exact Finset.mem_filter.mpr ⟨hin, Nat.lt_succ_self k⟩
          · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,
              Nat.lt_succ_of_lt (Finset.mem_filter.mp h).2⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnot] at hc
        omega
      · have s3' : (UB k).card = (UB (k + 1)).card := s3 hin
        have hc : (Xs.filter (fun i => i.val < k)).card ≤
            (Xs.filter (fun i => i.val < k + 1)).card :=
          Finset.card_le_card (fun i hi => Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hi).1, Nat.lt_succ_of_lt (Finset.mem_filter.mp hi).2⟩)
        omega
  refine ⟨stepJ, h0card, ?_⟩
  have h1 := tele gs.length le_rfl
  have h2 := Finset.card_filter_le Xs (fun i => i.val < gs.length)
  rw [h0card] at h1
  omega

end PEqualNP.Outside.L_meta_1641

theorem PEqualNP.Outside.L_meta_1641 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card :=
  PEqualNP.Outside.L_meta_1641.main_aux
