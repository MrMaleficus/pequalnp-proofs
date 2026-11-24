import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1573

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

private lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
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

private lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

private lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
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
    ∀ t, (W gs x).getD t false = true → (W gs y).getD t false = true

private lemma mono_nil {n : ℕ} : Mono (n := n) [] := by
  intro x y hxy t ht
  obtain ⟨hlt, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, hlt⟩).trans (hxy _ hx)

private lemma mono_step {n : ℕ} (gs : List Gate) (g : Gate)
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

private lemma mono_all {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : Mono (n := n) gs := by
  induction gs using List.reverseRecOn with
  | nil => exact mono_nil
  | append_singleton gs g ih =>
    exact mono_step gs g (hg g (by simp)) (ih (fun g' hg' => hg g' (by simp [hg'])))

private lemma eval_W {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

private lemma eval_mono {n : ℕ} (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (h : Circuit.eval ⟨gs, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true := by
  rw [eval_W] at h ⊢
  exact mono_all gs (fun g hgm => (hg g hgm).1) x y hxy o h

private lemma fact1 (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) :
    ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)),
      ∀ p ∈ L l, ∀ l2 ∈ ({4, 10, 12} : Finset (Fin 13)), l2 ≠ l →
        (∀ v : Fin 13, (v = p ∨ (p ≠ 0 ∧ v = 1)) → v ∉ L m) ∨
        (∀ v : Fin 13, (v = p ∨ (p ≠ 0 ∧ v = 1)) → v ∉ L l2) := by
  have hLe : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  subst hLe
  decide +kernel

private lemma fact2 (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) :
    ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
      ∀ p ∈ L m, ∀ m2 ∈ ({1, 5, 11} : Finset (Fin 13)), m2 ≠ m →
        (∀ v : Fin 13, (v = p ∨ (p ≠ 1 ∧ v = 0)) → v ∉ L l) ∨
        (∀ v : Fin 13, (v = p ∨ (p ≠ 1 ∧ v = 0)) → v ∉ L m2) := by
  have hLe : L = fun t => {t, t + 1, t + 3, t + 9} := funext hL
  subst hLe
  decide +kernel

theorem main_aux : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false → (∃ p ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) →
      ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l'))) = true) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → (∃ p ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) →
      ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m'))) = true) := by
  intro L hL gates g hg
  refine ⟨?_, ?_⟩
  · intro m hm l hl hfalse hex l2 hl2 hne
    obtain ⟨p, hp, htrue⟩ := hex
    rcases fact1 L hL m hm l hl p hp l2 hl2 hne with h | h
    · have hc := eval_mono gates g hg _ (fun v : Fin 13 => decide (v ∉ L m))
        (fun i hi => decide_eq_true (h i (of_decide_eq_true hi))) htrue
      rw [hfalse] at hc
      exact Bool.noConfusion hc
    · exact eval_mono gates g hg _ (fun v : Fin 13 => decide (v ∉ L l2))
        (fun i hi => decide_eq_true (h i (of_decide_eq_true hi))) htrue
  · intro l hl m hm hfalse hex m2 hm2 hne
    obtain ⟨p, hp, htrue⟩ := hex
    rcases fact2 L hL l hl m hm p hp m2 hm2 hne with h | h
    · have hc := eval_mono gates g hg _ (fun v : Fin 13 => decide (v ∉ L l))
        (fun i hi => decide_eq_true (h i (of_decide_eq_true hi))) htrue
      rw [hfalse] at hc
      exact Bool.noConfusion hc
    · exact eval_mono gates g hg _ (fun v : Fin 13 => decide (v ∉ L m2))
        (fun i hi => decide_eq_true (h i (of_decide_eq_true hi))) htrue

end PEqualNP.Outside.L_meta_1573

theorem PEqualNP.Outside.L_meta_1573 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false → (∃ p ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) →
      ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l'))) = true) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → (∃ p ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) →
      ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m'))) = true) :=
  PEqualNP.Outside.L_meta_1573.main_aux
