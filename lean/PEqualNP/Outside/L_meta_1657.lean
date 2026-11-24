import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1657

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

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma W_prefix {n : ℕ} (gs rest : List Gate) (x : Fin n → Bool) (t : ℕ)
    (ht : t < n + gs.length) :
    (W (gs ++ rest) x).getD t false = (W gs x).getD t false := by
  induction rest using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton rest g ih =>
    have hne : ¬ t = n + (gs ++ rest).length := by
      rw [List.length_append]
      omega
    rw [← List.append_assoc, W_val, if_neg hne]
    exact ih

private lemma gate_eq {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < gs.length)
    (hord : ∀ w ∈ (gs[i]'hi).inputs, w < n + i) :
    (W gs x).getD (n + i) false =
      (gs[i]'hi).op.eval ((gs[i]'hi).inputs.map fun k => (W gs x).getD k false) := by
  have h1 := W_prefix (gs.take (i + 1)) (gs.drop (i + 1)) x (n + i)
    (by rw [List.length_take]; omega)
  rw [List.take_append_drop] at h1
  have hlen : n + i = n + (gs.take i).length := by
    rw [List.length_take]
    omega
  rw [h1, List.take_succ_eq_append_getElem hi, W_val, if_pos hlen]
  congr 1
  apply List.map_congr_left
  intro k hk
  have h2 := W_prefix (gs.take i) (gs.drop i) x k
    (by rw [List.length_take]; have := hord k hk; omega)
  rw [List.take_append_drop] at h2
  exact h2.symm

private lemma mono_gen {N : ℕ} (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
    (F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩)
    (F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x = (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x))
    (F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false)
    (hord : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (B : ℕ)
    (good : ∀ i : Fin gates.length, N + (i : ℕ) < B →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or ∨ ev (N + (i : ℕ)) y = true) :
    ∀ w : ℕ, w < B → ev w x = true → ev w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwB hx
    by_cases h1 : w < N
    · rw [F_in w h1 x] at hx
      rw [F_in w h1 y]
      exact hxy _ hx
    · by_cases h2 : w < N + gates.length
      · obtain ⟨i, hi⟩ : ∃ i : Fin gates.length, w = N + (i : ℕ) :=
          ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
        subst hi
        rcases good i hwB with hand | hor | ht
        · rw [F_gate i x, hand] at hx
          rw [F_gate i y, hand]
          exact (all_true _ _).mpr (fun k hk =>
            ih k (hord i k hk) (lt_trans (hord i k hk) hwB) ((all_true _ _).mp hx k hk))
        · rw [F_gate i x, hor] at hx
          rw [F_gate i y, hor]
          obtain ⟨k, hk, hkt⟩ := (any_true _ _).mp hx
          exact (any_true _ _).mpr
            ⟨k, hk, ih k (hord i k hk) (lt_trans (hord i k hk) hwB) hkt⟩
        · exact ht
      · rw [F_out w (by omega) x] at hx
        exact Bool.noConfusion hx

private lemma and_eval (l : List Bool) : GateOp.and.eval l = l.all id := rfl

private lemma or_eval (l : List Bool) : GateOp.or.eval l = l.any id := rfl

private lemma W_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (W gs x).getD k false = x ⟨k, hk⟩ := by
  have e := W_prefix [] gs x k (by simpa using hk)
  rw [List.nil_append] at e
  rw [e]
  exact ofFn_getD_val x ⟨k, hk⟩

private lemma set_gate_ne {n : ℕ} (gs : List Gate) (g : Gate) (j : ℕ) (x : Fin n → Bool) (i : ℕ)
    (hi : i < gs.length) (hne : j ≠ i) (hord : ∀ w ∈ (gs[i]'hi).inputs, w < n + i) :
    (W (gs.set j g) x).getD (n + i) false =
      (gs[i]'hi).op.eval ((gs[i]'hi).inputs.map fun k => (W (gs.set j g) x).getD k false) := by
  have hi' : i < (gs.set j g).length := by rw [List.length_set]; exact hi
  have hg : (gs.set j g)[i]'hi' = gs[i]'hi := List.getElem_set_ne hne hi'
  have e := gate_eq (gs.set j g) x i hi' (by rw [hg]; exact hord)
  rw [hg] at e
  exact e

private lemma set_gate_self {n : ℕ} (gs : List Gate) (g : Gate) (j : ℕ) (x : Fin n → Bool)
    (hj : j < gs.length) (hord : ∀ w ∈ g.inputs, w < n + j) :
    (W (gs.set j g) x).getD (n + j) false =
      g.op.eval (g.inputs.map fun k => (W (gs.set j g) x).getD k false) := by
  have hj' : j < (gs.set j g).length := by rw [List.length_set]; exact hj
  have hg : (gs.set j g)[j]'hj' = g := List.getElem_set_self hj'
  have e := gate_eq (gs.set j g) x j hj' (by rw [hg]; exact hord)
  rw [hg] at e
  exact e

private lemma set_or_nil {n : ℕ} (gs : List Gate) (j : ℕ) (x : Fin n → Bool)
    (hj : j < gs.length) :
    (W (gs.set j ⟨GateOp.or, []⟩) x).getD (n + j) false = false := by
  have e := set_gate_self gs ⟨GateOp.or, []⟩ j x hj (fun w hw => by simp at hw)
  rw [e]
  rfl

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
  intro q N L va vb vc sa sb sc hq hN hcard hint hjoin hnc hbsa hcsa hcsb hasb hasc hbsc
    gates o j h hg hord hjnot hjuniq hhj hjin hout hread ev ev' hev hev' hvert hside
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  have E' : ∀ (w : ℕ) (x : Fin N → Bool),
      ev' w x = (W (gates.set (j : ℕ) ⟨GateOp.or, []⟩) x).getD w false :=
    fun w x => hev' w x
  have F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩ := by
    intro k hk x
    rw [E]
    exact W_in gates x k hk
  have F_in' : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev' k x = x ⟨k, hk⟩ := by
    intro k hk x
    rw [E']
    exact W_in _ x k hk
  have F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false := by
    intro k hk x
    rw [E]
    exact List.getD_eq_default _ _ (by rw [W_len]; omega)
  have F_out' : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev' k x = false := by
    intro k hk x
    rw [E']
    exact List.getD_eq_default _ _ (by rw [W_len, List.length_set]; omega)
  have F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x) := by
    intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
  have F_gate' : ∀ (i : Fin gates.length) (x : Fin N → Bool), i ≠ j →
      ev' (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev' k x) := by
    intro i x hij
    have hne : (j : ℕ) ≠ (i : ℕ) := fun e => hij (Fin.ext e.symm)
    have e := set_gate_ne gates ⟨GateOp.or, []⟩ (j : ℕ) x i.val i.isLt hne (hord i)
    have hfun : (fun k => (W (gates.set (j : ℕ) ⟨GateOp.or, []⟩) x).getD k false) =
        fun k => ev' k x :=
      funext (fun k => (E' k x).symm)
    rw [hfun, ← E'] at e
    exact e
  have F_j' : ∀ x : Fin N → Bool, ev' (N + (j : ℕ)) x = false := by
    intro x
    rw [E']
    exact set_or_nil gates (j : ℕ) x j.isLt
  have hop : ∀ i : Fin gates.length, i ≠ j →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or := by
    intro i hij
    rcases (hg (gates.get i) (List.get_mem gates i)).1 with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact absurd (hjuniq i a) hij
  have hz : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = Bool.not (ev (N + (h : ℕ)) x) := by
    intro x
    obtain ⟨r, hr⟩ := hjin
    have e1 := F_gate j x
    rw [hjnot, hr] at e1
    exact e1
  have hzt : ∀ x : Fin N → Bool, ev (N + (h : ℕ)) x = false → ev (N + (j : ℕ)) x = true :=
    fun x hf => (hz x).trans (congrArg Bool.not hf)
  have hzf : ∀ x : Fin N → Bool, ev (N + (h : ℕ)) x = true → ev (N + (j : ℕ)) x = false :=
    fun x hf => (hz x).trans (congrArg Bool.not hf)
  have hlt : (h : ℕ) < (j : ℕ) := hhj
  have hmonoh : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev (N + (h : ℕ)) x = true → ev (N + (h : ℕ)) y = true := by
    intro x y hxy
    refine mono_gen gates ev F_in F_gate F_out hord x y hxy (N + (j : ℕ)) ?_ (N + (h : ℕ))
      (by omega)
    intro i hi
    have hij : i ≠ j := by
      intro e
      rw [e] at hi
      exact lt_irrefl _ hi
    rcases hop i hij with a | a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
  have hev_out : ∀ (t : Fin N) (x : Fin N → Bool),
      ev (o t) x = decide (∃ v ∈ L t, x v = true) :=
    fun t x => (hev (o t) x).trans (hout t x)
  have C1 : ∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true := by
    intro w x
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hx
      by_cases h1 : w < N
      · rw [F_in' w h1 x] at hx
        rw [F_in w h1 x]
        exact hx
      · by_cases h2 : w < N + gates.length
        · obtain ⟨i, hi⟩ : ∃ i : Fin gates.length, w = N + (i : ℕ) :=
            ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
          subst hi
          by_cases hij : i = j
          · rw [hij, F_j' x] at hx
            exact Bool.noConfusion hx
          · rcases hop i hij with hand | hor
            · rw [F_gate' i x hij, hand, and_eval] at hx
              rw [F_gate i x, hand, and_eval]
              exact (all_true _ _).mpr (fun k hk =>
                ih k (hord i k hk) ((all_true _ _).mp hx k hk))
            · rw [F_gate' i x hij, hor, or_eval] at hx
              rw [F_gate i x, hor, or_eval]
              obtain ⟨k, hk, hkt⟩ := (any_true _ _).mp hx
              exact (any_true _ _).mpr ⟨k, hk, ih k (hord i k hk) hkt⟩
        · rw [F_out' w (by omega) x] at hx
          exact Bool.noConfusion hx
  have C2 : ∀ (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ∀ w : ℕ, ev' w x = ev w x := by
    intro x hhx w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases h1 : w < N
      · rw [F_in' w h1 x, F_in w h1 x]
      · by_cases h2 : w < N + gates.length
        · obtain ⟨i, hi⟩ : ∃ i : Fin gates.length, w = N + (i : ℕ) :=
            ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
          subst hi
          by_cases hij : i = j
          · rw [hij, F_j' x]
            exact (hzf x hhx).symm
          · rw [F_gate' i x hij, F_gate i x]
            congr 1
            apply List.map_congr_left
            intro k hk
            exact ih k (hord i k hk)
        · rw [F_out' w (by omega) x, F_out w (by omega) x]
  have C3 : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false := by
    intro i x hmem
    have hand := hread i hmem
    have hij : i ≠ j := by
      intro e
      rw [e, hjnot] at hand
      exact GateOp.noConfusion hand
    apply Bool.eq_false_iff.mpr
    intro ht
    rw [F_gate' i x hij, hand, and_eval] at ht
    have h3 := (all_true _ _).mp ht _ hmem
    exact Bool.noConfusion (h3.symm.trans (F_j' x))
  have D : ∀ (x : Fin N → Bool) (w : ℕ), ev w x = true → ev' w x = false →
      w = N + (j : ℕ) ∨ ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧
        ev (N + (i : ℕ)) x = true := by
    intro x w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro ht hf
      by_cases h1 : w < N
      · rw [F_in w h1 x] at ht
        rw [F_in' w h1 x] at hf
        exact Bool.noConfusion (ht.symm.trans hf)
      · by_cases h2 : w < N + gates.length
        · obtain ⟨i, hi⟩ : ∃ i : Fin gates.length, w = N + (i : ℕ) :=
            ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
          subst hi
          by_cases hij : i = j
          · exact Or.inl (by rw [hij])
          · have ht0 := ht
            rcases hop i hij with hand | hor
            · rw [F_gate i x, hand, and_eval] at ht
              rw [F_gate' i x hij, hand, and_eval] at hf
              have hall := (all_true _ _).mp ht
              have hex : ∃ k ∈ (gates.get i).inputs, ev' k x = false := by
                by_contra hcon
                have hall' : ∀ k ∈ (gates.get i).inputs, ev' k x = true := by
                  intro k hk
                  by_contra hk2
                  exact hcon ⟨k, hk, Bool.eq_false_iff.mpr hk2⟩
                exact Bool.noConfusion (((all_true _ _).mpr hall').symm.trans hf)
              obtain ⟨k, hk, hkf⟩ := hex
              rcases ih k (hord i k hk) (hall k hk) hkf with e | hr
              · subst e
                exact Or.inr ⟨i, hk, ht0⟩
              · exact Or.inr hr
            · rw [F_gate i x, hor, or_eval] at ht
              rw [F_gate' i x hij, hor, or_eval] at hf
              obtain ⟨k, hk, hkt⟩ := (any_true _ _).mp ht
              have hkf : ev' k x = false := by
                apply Bool.eq_false_iff.mpr
                intro hk2
                exact Bool.noConfusion (((any_true _ _).mpr ⟨k, hk, hk2⟩).symm.trans hf)
              rcases ih k (hord i k hk) hkt hkf with e | hr
              · subst e
                have hand := hread i hk
                rw [hor] at hand
                exact GateOp.noConfusion hand
              · exact Or.inr hr
        · rw [F_out w (by omega) x] at ht
          exact Bool.noConfusion ht
  have C4 : ∀ (t P : Fin N), P ∈ L t →
      ev' (o t) (fun v : Fin N => decide (v = P)) = false →
      ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧
        ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true := by
    intro t P hP hf
    have ht : ev (o t) (fun v : Fin N => decide (v = P)) = true := by
      rw [hev_out]
      exact decide_eq_true ⟨P, hP, by simp⟩
    rcases D _ (o t) ht hf with e | hr
    · exfalso
      have h0 : ev (o t) (fun _ : Fin N => false) = false := by
        rw [hev_out]
        exact decide_eq_false (by rintro ⟨v, _, hv⟩; simp at hv)
      rw [e] at h0 ht
      have hh0 : ev (N + (h : ℕ)) (fun _ : Fin N => false) = true := by
        by_contra hne
        have hf0 : ev (N + (h : ℕ)) (fun _ : Fin N => false) = false :=
          Bool.eq_false_iff.mpr hne
        exact Bool.noConfusion ((hzt _ hf0).symm.trans h0)
      have hhP := hmonoh (fun _ : Fin N => false) (fun v : Fin N => decide (v = P))
        (fun v hv => by simp at hv) hh0
      exact Bool.noConfusion (ht.symm.trans (hzf _ hhP))
    · exact hr
  have C5 : ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t →
      ev' (o t) (fun uu : Fin N => decide (uu = v)) = true := by
    intro t v hv hvL
    have hv' : v = va ∨ v = vb ∨ v = vc := by
      simpa using hv
    have hh := (hvert v).mpr hv'
    rw [C2 _ hh (o t), hev_out]
    exact decide_eq_true ⟨v, hvL, by simp⟩
  exact ⟨C1, fun w x hx => C2 x hx w, C3, C4, C5⟩

end PEqualNP.Outside.L_meta_1657

theorem PEqualNP.Outside.L_meta_1657 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (va vb vc sa sb sc : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    (∀ t : Fin N, ¬ (va ∈ L t ∧ vb ∈ L t ∧ vc ∈ L t)) →
    vb ∈ L sa → vc ∈ L sa → vc ∈ L sb → va ∈ L sb → va ∈ L sc → vb ∈ L sc →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
    ∀ ev ev' : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, w⟩ (List.ofFn x)) →
    (∀ p : Fin N, ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = true ↔ (p = va ∨ p = vb ∨ p = vc)) →
    (∀ (i : Fin gates.length) (P : Fin N), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true →
      (P ∈ L sa ∨ P ∈ L sb ∨ P ∈ L sc) ∧ P ≠ va ∧ P ≠ vb ∧ P ≠ vc) →
    (∀ (w : ℕ) (x : Fin N → Bool), ev' w x = true → ev w x = true) ∧ (∀ (w : ℕ) (x : Fin N → Bool), ev (N + (h : ℕ)) x = true → ev' w x = ev w x) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool), (N + (j : ℕ)) ∈ (gates.get i).inputs → ev' (N + (i : ℕ)) x = false) ∧
    (∀ (t P : Fin N), P ∈ L t → ev' (o t) (fun v : Fin N => decide (v = P)) = false → ∃ i : Fin gates.length, (N + (j : ℕ)) ∈ (gates.get i).inputs ∧ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = P)) = true) ∧
    ∀ t : Fin N, ∀ v ∈ ({va, vb, vc} : Finset (Fin N)), v ∈ L t → ev' (o t) (fun uu : Fin N => decide (uu = v)) = true :=
  PEqualNP.Outside.L_meta_1657.main_aux
