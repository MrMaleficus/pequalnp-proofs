import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def V (gates : List Gate) (x : Fin 13 → Bool) (u : ℕ) : Bool :=
  Circuit.eval ⟨gates, u⟩ (List.ofFn x)

lemma V_eq (gates : List Gate) (x : Fin 13 → Bool) (u : ℕ) :
    V gates x u = (gates.foldl stepWire (List.ofFn x)).getD u false := rfl

lemma V_gate (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gates.length) :
    V gates x (13 + k) = (gates[k]).op.eval ((gates[k]).inputs.map fun i =>
      if i < 13 + k then V gates x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates gates k hk
  rw [hgj]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = 13 + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : V gates x (13 + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    rw [V_eq, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (13 + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < 13 + k
  · simp only [hi, ↓reduceIte]
    rw [V_eq, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma ofFn_getD (n : ℕ) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

lemma V_input (gates : List Gate) (x : Fin 13 → Bool) (u : ℕ) (hu : u < 13) :
    V gates x u = x ⟨u, hu⟩ := by
  rw [V_eq, foldl_stepWire_getD_lt gates (List.ofFn x) u (by rw [List.length_ofFn]; exact hu)]
  exact ofFn_getD 13 x u hu

lemma V_out (gates : List Gate) (x : Fin 13 → Bool) (u : ℕ) (hu : 13 + gates.length ≤ u) :
    V gates x u = false := by
  rw [V_eq]
  exact getD_ge_length _ _ (by rw [foldl_stepWire_length, List.length_ofFn]; exact hu)

lemma V_and (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.and) :
    V gates x (13 + k) = true ↔ ∀ a ∈ (gates[k]).inputs, a < 13 + k ∧ V gates x a = true := by
  rw [V_gate gates x k hk, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro h a ha
    have h1 := h a ha
    by_cases hlt : a < 13 + k
    · simp only [hlt, ite_true] at h1
      exact ⟨hlt, h1⟩
    · simp [hlt] at h1
  · intro h a ha
    obtain ⟨hlt, hv⟩ := h a ha
    simp only [hlt, ite_true]
    exact hv

lemma V_or (gates : List Gate) (x : Fin 13 → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : (gates[k]).op = GateOp.or) :
    V gates x (13 + k) = true ↔ ∃ a ∈ (gates[k]).inputs, a < 13 + k ∧ V gates x a = true := by
  rw [V_gate gates x k hk, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨a, ha, h1⟩
    by_cases hlt : a < 13 + k
    · simp only [hlt, ite_true] at h1
      exact ⟨a, ha, hlt, h1⟩
    · simp [hlt] at h1
  · rintro ⟨a, ha, hlt, hv⟩
    refine ⟨a, ha, ?_⟩
    simp only [hlt, ite_true]
    exact hv

theorem mono (gates : List Gate)
    (hAO : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ u : ℕ, V gates x u = true → V gates y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < 13
    · rw [V_input gates _ u hun] at hu ⊢
      exact hxy _ hu
    · obtain ⟨k, rfl⟩ : ∃ k, u = 13 + k := ⟨u - 13, by omega⟩
      by_cases hk : k < gates.length
      · rcases hAO _ (List.getElem_mem hk) with hop | hop
        · rw [V_and gates _ k hk hop] at hu ⊢
          intro a ha
          exact ⟨(hu a ha).1, ih a (hu a ha).1 (hu a ha).2⟩
        · rw [V_or gates _ k hk hop] at hu ⊢
          obtain ⟨a, ha, hlt, hv⟩ := hu
          exact ⟨a, ha, hlt, ih a hlt hv⟩
      · exfalso
        rw [V_out gates x _ (by omega)] at hu
        exact Bool.false_ne_true hu

theorem atom (gates : List Gate)
    (hAO : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (x : Fin 13 → Bool) :
    ∀ u : ℕ, V gates x u = true →
      ∃ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S →
          (gates.get i).op = GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧
        (Y < 13 ∨ ∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = GateOp.and) ∧
        V gates x Y = true ∧ (∀ z : Fin 13 → Bool, V gates z Y = true → V gates z u = true) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < 13
    · exact ⟨u, fun S hS _ => hS, Or.inl hun, hu, fun z hz => hz⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = 13 + k := ⟨u - 13, by omega⟩
      by_cases hk : k < gates.length
      · rcases hAO _ (List.getElem_mem hk) with hop | hop
        · exact ⟨13 + k, fun S hS _ => hS, Or.inr ⟨⟨k, hk⟩, rfl, hop⟩, hu, fun z hz => hz⟩
        · have hu2 := (V_or gates x k hk hop).1 hu
          obtain ⟨a, ha, hlt, hv⟩ := hu2
          obtain ⟨Y, hYS, hYk, hYv, hYb⟩ := ih a hlt hv
          refine ⟨Y, ?_, hYk, hYv, ?_⟩
          · intro S hS hcl
            exact hYS S (hcl ⟨k, hk⟩ hS hop a ha) hcl
          · intro z hz
            exact (V_or gates z k hk hop).2 ⟨a, ha, hlt, hYb z hz⟩
      · exfalso
        rw [V_out gates x _ (by omega)] at hu
        exact Bool.false_ne_true hu

set_option maxRecDepth 100000 in
lemma fin_fact : ∀ t p q : Fin 13, t ≠ 0 → p ≠ q →
    (p = 0 ∨ p = 1 ∨ p = 3 ∨ p = 9) → (q = 0 ∨ q = 1 ∨ q = 3 ∨ q = 9) →
    (p = t ∨ p = t + 1 ∨ p = t + 3 ∨ p = t + 9) →
    (q = t ∨ q = t + 1 ∨ q = t + 3 ∨ q = t + 9) → False := by
  decide

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  intro L hL gates g t hAO2 _hwf ht h0 htt hcard
  have hAO : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hAO2 g hg).1
  have h0' : V gates (fun v : Fin 13 => decide (v ∉ L 0)) g = false := h0
  have htt' : V gates (fun v : Fin 13 => decide (v ∉ L t)) g = false := htt
  have hmemL : ∀ a p : Fin 13, p ∈ L a ↔ (p = a ∨ p = a + 1 ∨ p = a + 3 ∨ p = a + 9) := by
    intro a p
    rw [hL a]
    simp
  have hcard2 : 1 < ((L 0).filter (fun p => V gates
      (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0))) g = true)).card := hcard
  rw [Finset.one_lt_card] at hcard2
  obtain ⟨p, hp, q, hq, hpq⟩ := hcard2
  rw [Finset.mem_filter] at hp hq
  have hA : ∀ r : Fin 13, V gates
      (fun v : Fin 13 => decide (v = r ∨ ((r = 3 ∨ r = 9) ∧ v ∉ L 0))) g = true →
      r ∉ L t → (r = 3 ∨ r = 9) := by
    intro r hr hrt
    by_contra hne
    have := mono gates hAO _ (fun v : Fin 13 => decide (v ∉ L t)) (by
      intro v hv
      simp only [decide_eq_true_eq] at hv ⊢
      rcases hv with hv | hv
      · rw [hv]; exact hrt
      · exact absurd hv.1 hne) g hr
    rw [htt'] at this
    exact Bool.false_ne_true this
  have hex : ∃ s : Fin 13, s ∈ L 0 ∧ s ∉ L t ∧ V gates
      (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0))) g = true := by
    by_cases hpt : p ∈ L t
    · by_cases hqt : q ∈ L t
      · exfalso
        have h1 := (hmemL 0 p).1 hp.1
        have h2 := (hmemL 0 q).1 hq.1
        simp only [zero_add] at h1 h2
        exact fin_fact t p q ht hpq h1 h2 ((hmemL t p).1 hpt) ((hmemL t q).1 hqt)
      · exact ⟨q, hq.1, hqt, hq.2⟩
    · exact ⟨p, hp.1, hpt, hp.2⟩
  obtain ⟨s, hs0, hst, hsv⟩ := hex
  have hs39 := hA s hsv hst
  obtain ⟨Y, hYS, hYk, hYv, hYb⟩ := atom gates hAO _ g hsv
  have hY0 : V gates (fun v : Fin 13 => decide (v ∉ L 0)) Y = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have h1 := hYb _ hc
    rw [h0'] at h1
    exact Bool.false_ne_true h1
  have hYt : V gates (fun v : Fin 13 => decide (v ∉ L t)) Y = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have h1 := hYb _ hc
    rw [htt'] at h1
    exact Bool.false_ne_true h1
  rcases hYk with hlt | hand
  · exfalso
    have e0 := V_input gates (fun v : Fin 13 => decide (v ∉ L 0)) Y hlt
    have et := V_input gates (fun v : Fin 13 => decide (v ∉ L t)) Y hlt
    have es := V_input gates
      (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0))) Y hlt
    rw [e0] at hY0
    rw [et] at hYt
    rw [es] at hYv
    have m0 : (⟨Y, hlt⟩ : Fin 13) ∈ L 0 := not_not.1 (of_decide_eq_false hY0)
    have mt : (⟨Y, hlt⟩ : Fin 13) ∈ L t := not_not.1 (of_decide_eq_false hYt)
    have hor : (⟨Y, hlt⟩ : Fin 13) = s ∨ ((s = 3 ∨ s = 9) ∧ (⟨Y, hlt⟩ : Fin 13) ∉ L 0) :=
      of_decide_eq_true hYv
    rcases hor with hv | hv
    · rw [hv] at mt
      exact hst mt
    · exact hv.2 m0
  · exact ⟨Y, hYS, hand, hY0, hYt, s, hs39, hst, hYv⟩

end PEqualNP.Outside.L_meta_1577

theorem PEqualNP.Outside.L_meta_1577 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true :=
  PEqualNP.Outside.L_meta_1577.main_aux
