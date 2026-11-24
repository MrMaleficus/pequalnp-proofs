import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1656

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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

private lemma gate_inputs_ao {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hj : w - n < C.gates.length)
    (hop2 : (C.gates[w - n]'hj).op = GateOp.and ∨ (C.gates[w - n]'hj).op = GateOp.or)
    (hlen : (C.gates[w - n]'hj).inputs.length ≤ 2) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'hj
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    have hop2' : g.op = GateOp.and ∨ g.op = GateOp.or := hop2
    rcases hop2' with hop | hop
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hx ⊢
      rintro b ⟨r, hrm, rfl⟩
      exact hr r hrm (hx _ ⟨r, hrm, rfl⟩)
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hx ⊢
      obtain ⟨b, ⟨r, hrm, rfl⟩, hb⟩ := hx
      exact ⟨_, ⟨r, hrm, rfl⟩, hr r hrm hb⟩

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]'hj) (List.getElem_mem _)
  exact gate_inputs_ao C w hn hw hj hop hlen

private lemma value_mono {n : ℕ} (C : Circuit)
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

private def Q {n : ℕ} (C : Circuit) (l y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  l.filter (fun p => value C (fun u : Fin n => decide (u ∈ y ∨ u = p)) w = true ∧
    value C (fun u : Fin n => decide (u ∈ y)) w = false)

private lemma mem_Q {n : ℕ} (C : Circuit) (l y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ Q C l y w ↔ p ∈ l ∧ value C (fun u : Fin n => decide (u ∈ y ∨ u = p)) w = true ∧
      value C (fun u : Fin n => decide (u ∈ y)) w = false := by
  simp [Q]

private def Merge {n : ℕ} (C : Circuit) (l y : Finset (Fin n)) (k : ℕ) : Prop :=
  ∃ g : Gate, C.gates[k]? = some g ∧ g.op = GateOp.or ∧
    value C (fun u : Fin n => decide (u ∈ y)) (n + k) = false ∧
    ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
      value C (fun u : Fin n => decide (u ∈ y ∨ u = p1)) i1 = true ∧
      value C (fun u : Fin n => decide (u ∈ y ∨ u = p2)) i2 = true

private lemma wire_step {n : ℕ} (C : Circuit) (l y : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (s : ℕ) :
    (∃ P : Finset ℕ, (∀ r ∈ P, r < s) ∧ Q C l y s ⊆ P.biUnion (Q C l y) ∧
      (P.card ≤ 1 ∨ (P.card ≤ 2 ∧ ∃ k, s = n + k ∧ Merge C l y k))) ∨ (Q C l y s).card ≤ 1 := by
  classical
  by_cases hn : s < n
  · right
    let p0 : Fin n := ⟨s, hn⟩
    have hs : Q C l y s ⊆ {p0} := by
      intro p hp
      obtain ⟨_, h1, h2⟩ := (mem_Q C l y s p).mp hp
      change value C _ p0 = true at h1
      change value C _ p0 = false at h2
      rw [input_value] at h1 h2
      have h1' := of_decide_eq_true h1
      have h2' := of_decide_eq_false h2
      rcases h1' with h | h
      · exact absurd h h2'
      · simp [h]
    exact (Finset.card_le_card hs).trans (by simp)
  by_cases hw : s < n + C.size
  swap
  · right
    have hE : Q C l y s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨_, h1, _⟩ := (mem_Q C l y s p).mp hp
      rw [missing_value C _ s (by omega)] at h1
      exact absurd h1 (by simp)
    simp [hE]
  have hj : s - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[s - n]'hj
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  have formula (z : Fin n → Bool) :
      value C z s = g.op.eval (g.inputs.map fun r => if r < s then value C z r else false) :=
    gate_value C z s (by omega) hw
  by_cases hy : value C (fun u : Fin n => decide (u ∈ y)) s = true
  · right
    have hE : Q C l y s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨_, _, h2⟩ := (mem_Q C l y s p).mp hp
      rw [hy] at h2
      exact absurd h2 (by simp)
    simp [hE]
  have hyf : value C (fun u : Fin n => decide (u ∈ y)) s = false := by simpa using hy
  rcases hop with hop | hop
  · have hex : ¬ (∀ a ∈ g.inputs,
        (if a < s then value C (fun u : Fin n => decide (u ∈ y)) a else false) = true) := by
      intro hall
      apply hy
      rw [formula, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro b ⟨r, hr, rfl⟩
      exact hall r hr
    obtain ⟨a, ha, hav⟩ : ∃ a ∈ g.inputs,
        ¬ (if a < s then value C (fun u : Fin n => decide (u ∈ y)) a else false) = true := by
      by_contra hcon
      apply hex
      intro a ha
      by_contra h
      exact hcon ⟨a, ha, h⟩
    by_cases has : a < s
    · left
      refine ⟨{a}, by simpa using has, ?_, Or.inl (by simp)⟩
      intro p hp
      obtain ⟨hpl, h1, h2⟩ := (mem_Q C l y s p).mp hp
      rw [formula, hop] at h1
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h1
      have h3 := h1 _ ⟨a, ha, rfl⟩
      rw [if_pos has] at h3 hav
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_singleton_self a,
        (mem_Q C l y a p).mpr ⟨hpl, h3, by simpa using hav⟩⟩
    · right
      have hE : Q C l y s = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨hpl, h1, h2⟩ := (mem_Q C l y s p).mp hp
        rw [formula, hop] at h1
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h1
        have h3 := h1 _ ⟨a, ha, rfl⟩
        rw [if_neg has] at h3
        exact absurd h3 (by simp)
      simp [hE]
  · have hall : ∀ a ∈ g.inputs, a < s →
        value C (fun u : Fin n => decide (u ∈ y)) a = false := by
      intro a ha has
      by_contra hc
      have hc' : value C (fun u : Fin n => decide (u ∈ y)) a = true := by simpa using hc
      apply hy
      rw [formula, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      exact ⟨_, ⟨a, ha, rfl⟩, by rw [if_pos has]; exact hc'⟩
    let P := (g.inputs.toFinset.filter (· < s)).filter (fun a => (Q C l y a).Nonempty)
    have hPlt : ∀ r ∈ P, r < s := fun r hr =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
    have hPc : P.card ≤ 2 :=
      ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans
        ((List.toFinset_card_le _).trans hlen)
    have hsub : Q C l y s ⊆ P.biUnion (Q C l y) := by
      intro p hp
      obtain ⟨hpl, h1, h2⟩ := (mem_Q C l y s p).mp hp
      rw [formula, hop] at h1
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h1
      obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
      by_cases has : a < s
      · rw [if_pos has] at hb
        have hqa : p ∈ Q C l y a := (mem_Q C l y a p).mpr ⟨hpl, hb, hall a ha has⟩
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, has⟩, ⟨p, hqa⟩⟩, hqa⟩
      · rw [if_neg has] at hb
        exact absurd hb (by simp)
    left
    refine ⟨P, hPlt, hsub, ?_⟩
    by_cases hP1 : P.card ≤ 1
    · exact Or.inl hP1
    · right
      refine ⟨hPc, s - n, by omega, ?_⟩
      obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
      obtain ⟨hm1, ⟨p1, hp1⟩⟩ := Finset.mem_filter.mp hi1
      obtain ⟨hm2, ⟨p2, hp2⟩⟩ := Finset.mem_filter.mp hi2
      obtain ⟨hl1, hv1, _⟩ := (mem_Q C l y i1 p1).mp hp1
      obtain ⟨hl2, hv2, _⟩ := (mem_Q C l y i2 p2).mp hp2
      have hwe : n + (s - n) = s := by omega
      refine ⟨g, List.getElem?_eq_getElem hj, hop, ?_,
        i1, List.mem_toFinset.mp (Finset.mem_filter.mp hm1).1,
        i2, List.mem_toFinset.mp (Finset.mem_filter.mp hm2).1, hne, p1, hl1, p2, hl2, hv1, hv2⟩
      rw [hwe]
      exact hyf

private lemma cutQ {n : ℕ} (C : Circuit) (l y : Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (s : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w < s) :
    ∃ M : Finset ℕ, (∀ k ∈ M, n + k < s ∧ Merge C l y k) ∧
      (F.biUnion (Q C l y)).card ≤ F.card + M.card := by
  classical
  induction s generalizing F with
  | zero =>
    have hE : F = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => by have := hF w hw; omega)
    exact ⟨∅, by simp, by simp [hE]⟩
  | succ s ih =>
    by_cases hs : s ∈ F
    swap
    · obtain ⟨M, hM, hc⟩ := ih F (fun w hw => by
        have h1 := hF w hw
        have h2 : w ≠ s := fun e => hs (e ▸ hw)
        omega)
      exact ⟨M, fun k hk => ⟨by have := (hM k hk).1; omega, (hM k hk).2⟩, hc⟩
    have hFe : ∀ w ∈ F.erase s, w < s := by
      intro w hw
      have h1 := hF w (Finset.mem_erase.mp hw).2
      have h2 := (Finset.mem_erase.mp hw).1
      omega
    have he := Finset.card_erase_add_one hs
    rcases wire_step C l y hG s with ⟨P, hPlt, hsub, hcase⟩ | hsmall
    · let F' := F.erase s ∪ P
      have hF' : ∀ w ∈ F', w < s := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFe w hw
        · exact hPlt w hw
      obtain ⟨M, hM, hc⟩ := ih F' hF'
      have hbi : F.biUnion (Q C l y) ⊆ F'.biUnion (Q C l y) := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases hws : w = s
        · rw [hws] at hpw
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hsub hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hws, hw⟩), hpw⟩
      have hle := Finset.card_le_card hbi
      have hu : F'.card ≤ (F.erase s).card + P.card := Finset.card_union_le _ _
      rcases hcase with hP1 | ⟨hP2, k, hk, hmerge⟩
      · exact ⟨M, fun k hk => ⟨by have := (hM k hk).1; omega, (hM k hk).2⟩, by omega⟩
      · have hkM : k ∉ M := fun hkm => by have := (hM k hkm).1; omega
        refine ⟨insert k M, ?_, ?_⟩
        · intro k' hk'
          rcases Finset.mem_insert.mp hk' with hkk | hk'
          · rw [hkk]
            exact ⟨by omega, hmerge⟩
          · exact ⟨by have := (hM k' hk').1; omega, (hM k' hk').2⟩
        · rw [Finset.card_insert_of_notMem hkM]
          omega
    · obtain ⟨M, hM, hc⟩ := ih (F.erase s) hFe
      have hbi : F.biUnion (Q C l y) ⊆ (F.erase s).biUnion (Q C l y) ∪ Q C l y s := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases hws : w = s
        · rw [hws] at hpw
          exact Finset.mem_union_right _ hpw
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_erase.mpr ⟨hws, hw⟩, hpw⟩)
      have hle := (Finset.card_le_card hbi).trans (Finset.card_union_le _ _)
      exact ⟨M, fun k hk => ⟨by have := (hM k hk).1; omega, (hM k hk).2⟩, by omega⟩

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (l y : Finset (Fin n)),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD out false = false →
  (∀ p ∈ l, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = p)))).getD out false = true) →
  ∃ s : Finset ℕ, l.card ≤ s.card + 1 ∧ ∀ k ∈ s, ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g ∧
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD (n + k) false = false ∧
    ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p1)))).getD i1 false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p2)))).getD i2 false = true := by
  classical
  intro n gates out l y hG _ hy hl
  obtain ⟨M, hM, hc⟩ := cutQ (n := n) ⟨gates, 0⟩ l y hG (out + 1) {out} (by simp)
  have hQ : Q (n := n) ⟨gates, 0⟩ l y out = l := by
    unfold Q
    apply Finset.filter_true_of_mem
    intro p hp
    refine ⟨?_, hy⟩
    exact value_mono ⟨gates, 0⟩ hG (fun u => decide (u = p)) (fun u => decide (u ∈ y ∨ u = p))
      (fun q hq => by simp [of_decide_eq_true hq]) out (hl p hp)
  simp only [Finset.singleton_biUnion, Finset.card_singleton, hQ] at hc
  exact ⟨M, by omega, fun k hk => (hM k hk).2⟩

end PEqualNP.Outside.L_meta_1656

theorem PEqualNP.Outside.L_meta_1656 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (l y : Finset (Fin n)),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD out false = false →
  (∀ p ∈ l, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = p)))).getD out false = true) →
  ∃ s : Finset ℕ, l.card ≤ s.card + 1 ∧ ∀ k ∈ s, ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g ∧
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y)))).getD (n + k) false = false ∧
    ∃ i1 ∈ g.inputs, ∃ i2 ∈ g.inputs, i1 ≠ i2 ∧ ∃ p1 ∈ l, ∃ p2 ∈ l,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p1)))).getD i1 false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ y ∨ u = p2)))).getD i2 false = true :=
  PEqualNP.Outside.L_meta_1656.main_aux
