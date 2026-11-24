import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1568

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

lemma mono_all {n : ℕ} (gs : List Gate) :
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => intro _; exact mono_nil
  | append_singleton l a ih =>
    intro h
    exact mono_step l a (h a (by simp)) (ih (fun g hg => h g (by simp [hg])))

lemma eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (h : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hx : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true :=
  mono_all gs h x y hxy o hx

set_option maxRecDepth 100000 in
lemma cap_card : ∀ t u : Fin 13, t ≠ u →
    (({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∩ {u, u + 1, u + 3, u + 9}).card ≤ 1 := by
  decide

lemma key (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List Gate) (g : ℕ) (a b : Fin 13)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hab : a ≠ b)
    (hcb : Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L b))) = false)
    (hw : 2 ≤ ((L a).filter (fun p => Circuit.eval ⟨gates, g⟩ (List.ofFn (T a p)) = true)).card) :
    ∃ p ∈ L a \ L b, ∃ v ∈ L b, (T a p) v = true := by
  have hwit : ∀ p : Fin 13, Circuit.eval ⟨gates, g⟩ (List.ofFn (T a p)) = true →
      ∃ v ∈ L b, (T a p) v = true := by
    intro p hp
    by_contra hno
    have h2 := eval_mono gates g hg (T a p) (fun v : Fin 13 => decide (v ∉ L b))
      (fun i hi => by
        rw [decide_eq_true_eq]
        intro hib
        exact hno ⟨i, hib, hi⟩) hp
    exact Bool.noConfusion (h2.symm.trans hcb)
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le Nat.one_lt_two hw)
  rw [Finset.mem_filter] at hp hq
  have hcap := cap_card a b hab
  rw [← hL a, ← hL b] at hcap
  by_cases hpb : p ∈ L b
  · have hqb : q ∉ L b := by
      intro hqb
      exact hpq (Finset.card_le_one.mp hcap p (Finset.mem_inter.mpr ⟨hp.1, hpb⟩) q
        (Finset.mem_inter.mpr ⟨hq.1, hqb⟩))
    exact ⟨q, Finset.mem_sdiff.mpr ⟨hq.1, hqb⟩, hwit q hq.2⟩
  · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp.1, hpb⟩, hwit p hp.2⟩

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t u : Fin 13),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → t ≠ u →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L u))) = false →
    2 ≤ ((L t).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card →
    2 ≤ ((L u).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T u p)) = true)).card →
    (∃ p ∈ L t \ L u, ∃ v ∈ L u, (T t p) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (T u p) v = true) := by
  intro L hL T gates g t u hT hg htu hct hcu hwt hwu
  exact ⟨key L hL T gates g t u (fun g hgm => (hg g hgm).1) htu hcu hwt,
    key L hL T gates g u t (fun g hgm => (hg g hgm).1) (Ne.symm htu) hct hwu⟩

end PEqualNP.Outside.L_meta_1568

theorem PEqualNP.Outside.L_meta_1568 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t u : Fin 13),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → t ≠ u →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L u))) = false →
    2 ≤ ((L t).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T t p)) = true)).card →
    2 ≤ ((L u).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (T u p)) = true)).card →
    (∃ p ∈ L t \ L u, ∃ v ∈ L u, (T t p) v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, (T u p) v = true) :=
  PEqualNP.Outside.L_meta_1568.main_aux
