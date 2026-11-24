import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1639

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def Mono {n : ℕ} (gs : List Gate) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (h : Mono (n := n) gs) :
    Mono (n := n) (gs ++ [g]) := by
  intro x y hxy t ht
  rw [W_val] at ht ⊢
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

lemma mono_all {n : ℕ} (gs : List Gate)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact mono_nil
  | append_singleton gs g ih =>
    exact mono_step gs g (h g (by simp)) (ih (fun g' hg' => h g' (by simp [hg'])))

lemma W_app_lt {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + pre.length) (post : List Gate) :
    (W (pre ++ post) x).getD t false = (W pre x).getD t false := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    rw [← List.append_assoc, W_val, if_neg (by rw [List.length_append]; omega)]
    exact ih

lemma wire_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    (W gs x).getD p.val false = x p := by
  have h := W_app_lt [] x p.val (by simpa using p.isLt) gs
  rw [List.nil_append] at h
  rw [h]
  exact ofFn_getD_val x p

lemma or_up_split {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool)
    (hor : g.op = GateOp.or) (a : ℕ) (ha : a ∈ g.inputs) (hlt : a < n + pre.length)
    (hv : (W (pre ++ g :: post) x).getD a false = true) :
    (W (pre ++ g :: post) x).getD (n + pre.length) false = true := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [e] at hv ⊢
  rw [W_app_lt (pre ++ [g]) x _ (by rw [List.length_append, List.length_singleton]; omega)] at hv ⊢
  rw [W_val] at hv ⊢
  rw [if_pos rfl, hor]
  rw [if_neg (by omega)] at hv
  exact (any_true _ _).mpr ⟨a, ha, hv⟩

lemma or_up {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length)
    (hor : (gs.get i).op = GateOp.or) (a : ℕ) (ha : a ∈ (gs.get i).inputs)
    (hlt : a < n + i.val) (hv : (W gs x).getD a false = true) :
    (W gs x).getD (n + i.val) false = true := by
  have hsplit : gs.take i.val ++ gs.get i :: gs.drop (i.val + 1) = gs := by
    rw [List.get_eq_getElem, ← List.drop_eq_getElem_cons i.isLt, List.take_append_drop]
  have hlen : (gs.take i.val).length = i.val := by
    rw [List.length_take]
    exact min_eq_left (le_of_lt i.isLt)
  have h := or_up_split (gs.take i.val) (gs.drop (i.val + 1)) (gs.get i) x hor a ha
    (by rw [hlen]; exact hlt) (by rw [hsplit]; exact hv)
  rw [hsplit, hlen] at h
  exact h

theorem main_aux : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    ∀ (t : Fin N) (y : Fin N), t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false → L t ∩ L i0 = {y} →
      (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p = y) ∧ (y ∉ T0 → ∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = false) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ hT0 _ gates u hops _ hwf h0 t y _ ht hy
  have h0w : (W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = false := h0
  have htw : (W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = false := ht
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpS := hp {w | ((W gates (fun v : Fin N => decide (v ∉ L i0))).getD w false = true →
        (W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
      ((W gates (fun v : Fin N => decide (v ∉ L t))).getD w false = true →
        (W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true)} ⟨id, id⟩ ?_
    · have hpS2 : ((W gates (fun v : Fin N => decide (v ∉ L i0))).getD p.val false = true →
          (W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
        ((W gates (fun v : Fin N => decide (v ∉ L t))).getD p.val false = true →
          (W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true) := hpS
      obtain ⟨h1, h2⟩ := hpS2
      have hp0 : p ∈ L i0 := by
        by_contra hc
        have hw : (W gates (fun v : Fin N => decide (v ∉ L i0))).getD p.val false = true := by
          rw [wire_input]
          simpa using hc
        rw [h1 hw] at h0w
        exact Bool.noConfusion h0w
      have hpt : p ∈ L t := by
        by_contra hc
        have hw : (W gates (fun v : Fin N => decide (v ∉ L t))).getD p.val false = true := by
          rw [wire_input]
          simpa using hc
        rw [h2 hw] at htw
        exact Bool.noConfusion htw
      have hmem : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hpt, hp0⟩
      rw [hy] at hmem
      exact Finset.mem_singleton.mp hmem
    · intro i hi hor a ha
      have hi2 : ((W gates (fun v : Fin N => decide (v ∉ L i0))).getD (N + i.val) false = true →
          (W gates (fun v : Fin N => decide (v ∉ L i0))).getD u false = true) ∧
        ((W gates (fun v : Fin N => decide (v ∉ L t))).getD (N + i.val) false = true →
          (W gates (fun v : Fin N => decide (v ∉ L t))).getD u false = true) := hi
      exact ⟨fun hv => hi2.1 (or_up gates _ i hor a ha (hwf i a ha) hv),
        fun hv => hi2.2 (or_up gates _ i hor a ha (hwf i a ha) hv)⟩
  · intro hyT x hx
    have hxt : x ∉ L t := by
      intro hxt
      have hmem : x ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hxt, hT0 hx⟩
      rw [hy] at hmem
      have hxy : x = y := Finset.mem_singleton.mp hmem
      exact hyT (hxy ▸ hx)
    show (W gates (fun v : Fin N => decide (v = x))).getD u false = false
    by_contra hc
    have hc2 : (W gates (fun v : Fin N => decide (v = x))).getD u false = true := by
      simpa using hc
    have hm := mono_all (n := N) gates (fun g hg => (hops g hg).1)
      (fun v => decide (v = x)) (fun v => decide (v ∉ L t))
      (by
        intro v hv
        have hvx : v = x := by simpa using hv
        rw [hvx]
        simpa using hxt) u hc2
    rw [hm] at htw
    exact Bool.noConfusion htw

end PEqualNP.Outside.L_meta_1639

theorem PEqualNP.Outside.L_meta_1639 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 1 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    ∀ (t : Fin N) (y : Fin N), t ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = false → L t ∩ L i0 = {y} →
      (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get i).inputs, e ∈ S) → (p : ℕ) ∈ S) → p = y) ∧ (y ∉ T0 → ∀ x ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v = x))) = false) :=
  PEqualNP.Outside.L_meta_1639.main_aux
