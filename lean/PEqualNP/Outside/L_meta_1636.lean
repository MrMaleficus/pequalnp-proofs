import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1636

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

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne h0 h1 T hT gates hg hin hord ev hev w
  have mono : ∀ x y : Fin N → Bool, (∀ i, x i = true → y i = true) →
      ev w x = true → ev w y = true := by
    intro x y hxy h
    rw [hev] at h ⊢
    exact eval_mono gates w hg x y hxy h
  have two : ∀ a b : Fin N, a ≠ b → ∀ p p' : Fin N, p ∈ L a → p ∈ L b → p' ∈ L a → p' ∈ L b →
      p = p' := by
    intro a b hab p p' ha hb ha' hb'
    have hc := hint a b hab
    rw [Finset.card_eq_one] at hc
    obtain ⟨c, hc⟩ := hc
    have e1 : p ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨ha, hb⟩
    have e2 : p' ∈ L a ∩ L b := Finset.mem_inter.mpr ⟨ha', hb'⟩
    rw [hc] at e1 e2
    rw [Finset.mem_singleton] at e1 e2
    rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · intro m l hm hl hfalse hex l2 hl2 hne2
    obtain ⟨p, hp, htrue⟩ := hex
    by_cases hpp : p = p0
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT l p v).mp hv with h | ⟨h, _, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩
        · exact decide_eq_true (by rw [h, hpp]; exact hm.2)
        · exact absurd hl.1 h
        · exact absurd hpp h
        · exact absurd h hl.2
      exact Bool.noConfusion (hfalse.symm.trans hc)
    · refine mono _ _ (fun v hv => ?_) htrue
      rcases (hT l p v).mp hv with h | ⟨h, _, _⟩ | ⟨_, _, _, h⟩ | ⟨_, h, _⟩
      · exact decide_eq_true (by
          rw [h]
          intro hin2
          exact hpp (two l l2 (Ne.symm hne2) p p0 hp hin2 hl.1 hl2.1))
      · exact absurd hl.1 h
      · exact decide_eq_true (by rw [h]; exact hl2.2)
      · exact absurd h hl.2
  · intro l m hl hm hfalse hex m2 hm2 hne2
    obtain ⟨p, hp, htrue⟩ := hex
    by_cases hpp : p = p1
    · exfalso
      have hc : ev w (fun v : Fin N => decide (v ∉ L l)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT m p v).mp hv with h | ⟨_, h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact decide_eq_true (by rw [h, hpp]; exact hl.2)
        · exact absurd hpp h
        · exact absurd h hm.2
        · exact absurd h hm.2
      exact Bool.noConfusion (hfalse.symm.trans hc)
    · refine mono _ _ (fun v hv => ?_) htrue
      rcases (hT m p v).mp hv with h | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
      · exact decide_eq_true (by
          rw [h]
          intro hin2
          exact hpp (two m m2 (Ne.symm hne2) p p1 hp hin2 hm.1 hm2.1))
      · exact decide_eq_true (by rw [h]; exact hm2.2)
      · exact absurd h hm.2
      · exact absurd h hm.2
  · intro m M hm hfalse hM
    have hMm : M ≠ m := by
      intro h
      rw [h] at hM
      exact hM.2 hm.1
    have hsub : (L M).filter (fun p => ev w (T M p) = true) ⊆ L M ∩ L m := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpM, htrue⟩ := hp
      rw [Finset.mem_inter]
      refine ⟨hpM, ?_⟩
      by_contra hpm
      have hc : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        refine mono _ _ (fun v hv => ?_) htrue
        rcases (hT M p v).mp hv with h | ⟨_, _, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
        · exact decide_eq_true (by rw [h]; exact hpm)
        · exact decide_eq_true (by rw [h]; exact hm.2)
        · exact absurd h hM.1
        · exact absurd h hM.1
      exact Bool.noConfusion (hfalse.symm.trans hc)
    calc ((L M).filter (fun p => ev w (T M p) = true)).card ≤ (L M ∩ L m).card :=
          Finset.card_le_card hsub
      _ = 1 := hint M m hMm

end PEqualNP.Outside.L_meta_1636

theorem PEqualNP.Outside.L_meta_1636 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) :=
  PEqualNP.Outside.L_meta_1636.main_aux
