import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1648

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

private theorem base : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot hjuniq hhj
    hjin hout ev hev hh0 hh1 hhp hhW
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  have F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩ := by
    intro k hk x
    have e := W_prefix [] gates x k (by simpa using hk)
    rw [List.nil_append] at e
    rw [E, e]
    exact ofFn_getD_val x ⟨k, hk⟩
  have F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false := by
    intro k hk x
    rw [E]
    exact List.getD_eq_default _ _ (by rw [W_len]; omega)
  have F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x) := by
    intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
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
  have P1 : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) →
      ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true := by
    intro x hx
    have hf : ev (N + (h : ℕ)) x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have h3 := hmonoh x (fun v : Fin N => decide (v ∉ L i0))
        (fun v hv => decide_eq_true (hx v hv)) ht
      exact Bool.noConfusion (h3.symm.trans hhW)
    exact ⟨hf, hzt x hf⟩
  refine ⟨P1, ?_, hzf _ hh0, hzf _ hh1, ?_⟩
  · intro w hw hw0 hw1
    have hf := hhp w hw0 hw1
    exact ⟨hf, hzt _ hf⟩
  · intro w x y hx hy hxy hw
    refine mono_gen gates ev F_in F_gate F_out hord x y hxy (w + 1) ?_ w (Nat.lt_succ_self w) hw
    intro i hi
    by_cases hij : i = j
    · refine Or.inr (Or.inr ?_)
      rw [hij]
      exact (P1 y hy).2
    · rcases hop i hij with a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)

private theorem cellB : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot hjuniq hhj
    hjin hout ev hev hh0 hh1 hhp hhW Sm Dm hSm hDm Vs hVs t
  have hmono := (base q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot
    hjuniq hhj hjin hout ev hev hh0 hh1 hhp hhW).2.2.2.2
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  have F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x =
        (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x) := by
    intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
  have C2 : ∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hS hv he
    have hsup : ∀ u : Fin N, (fun uu : Fin N => decide (uu = v)) u = true → u ∉ L i0 := by
      intro u hu
      have hu1 : decide (u = v) = true := hu
      have hu2 : u = v := of_decide_eq_true hu1
      rw [hu2]
      exact hv
    obtain ⟨u, hu, hux⟩ := (hSm t w).mp hS (fun uu : Fin N => decide (uu = v)) hsup he
    have hu1 : decide (u = v) = true := hux
    have hu2 : u = v := of_decide_eq_true hu1
    rw [← hu2]
    exact hu
  have C1 : ∀ (w : ℕ) (v : Fin N), Dm t w →
      ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t := by
    intro w v hD he
    obtain ⟨hS, hD2⟩ := (hDm t w).mp hD
    by_cases hv : v ∈ L i0
    · exact hD2 v hv he
    · exact C2 w v hS hv he
  refine ⟨C1, C2, ?_, ?_, ?_⟩
  · intro g hor
    have hup : ∀ e ∈ (gates.get g).inputs, ∀ x : Fin N → Bool, ev e x = true →
        ev (N + (g : ℕ)) x = true := by
      intro e he x hx
      rw [F_gate g x, hor]
      exact (any_true _ _).mpr ⟨e, he, hx⟩
    have hsm : Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e := by
      intro hS e he
      refine (hSm t e).mpr ?_
      intro x hx hex
      exact (hSm t (N + (g : ℕ))).mp hS x hx (hup e he x hex)
    refine ⟨hsm, ?_⟩
    intro hD e he
    obtain ⟨hS, hD2⟩ := (hDm t (N + (g : ℕ))).mp hD
    exact (hDm t e).mpr ⟨hsm hS e he, fun p hp hep => hD2 p hp (hup e he _ hep)⟩
  · intro g hand hS
    by_contra hno
    have hwit : ∀ e : ℕ, ∃ x : Fin N → Bool, e ∈ (gates.get g).inputs →
        ((∀ v : Fin N, x v = true → v ∉ L i0) ∧ ev e x = true ∧
          ∀ v : Fin N, v ∈ L t → x v = true → False) := by
      intro e
      by_cases he : e ∈ (gates.get g).inputs
      · by_contra hc
        apply hno
        refine ⟨e, he, (hSm t e).mpr ?_⟩
        intro x hx hex
        by_contra hc2
        exact hc ⟨x, fun _ => ⟨hx, hex, fun v hv hxv => hc2 ⟨v, hv, hxv⟩⟩⟩
      · exact ⟨fun _ => false, fun hin => absurd hin he⟩
    choose xf hxf using hwit
    obtain ⟨y, hydef⟩ : ∃ y : Fin N → Bool,
        ∀ v : Fin N, y v = (gates.get g).inputs.any (fun e => xf e v) := ⟨_, fun _ => rfl⟩
    have hy : ∀ v : Fin N, y v = true → ∃ e ∈ (gates.get g).inputs, xf e v = true := by
      intro v hv
      rw [hydef v] at hv
      exact List.any_eq_true.mp hv
    have hyW : ∀ v : Fin N, y v = true → v ∉ L i0 := by
      intro v hv
      obtain ⟨e, he, hxe⟩ := hy v hv
      exact (hxf e he).1 v hxe
    have hall : ev (N + (g : ℕ)) y = true := by
      rw [F_gate g y, hand]
      refine (all_true _ _).mpr (fun e he => ?_)
      refine hmono e (xf e) y (hxf e he).1 hyW ?_ (hxf e he).2.1
      intro v hv
      rw [hydef v]
      exact List.any_eq_true.mpr ⟨e, he, hv⟩
    obtain ⟨v, hv, hyv⟩ := (hSm t (N + (g : ℕ))).mp hS y hyW hall
    obtain ⟨e, he, hxe⟩ := hy v hyv
    exact (hxf e he).2.2 v hv hxe
  · intro w v hS hV
    rcases (hVs t w v).mp hV with ⟨hD, he⟩ | ⟨_, hv, he⟩
    · exact C1 w v hD he
    · exact C2 w v hS hv he

private lemma facts {N : ℕ} (gates : List Gate)
    (hord : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) :
    (∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩) ∧
    (∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x = (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x)) ∧
    (∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false) := by
  have E : ∀ (w : ℕ) (x : Fin N → Bool), ev w x = (W gates x).getD w false :=
    fun w x => hev w x
  refine ⟨?_, ?_, ?_⟩
  · intro k hk x
    have e := W_prefix [] gates x k (by simpa using hk)
    rw [List.nil_append] at e
    rw [E, e]
    exact ofFn_getD_val x ⟨k, hk⟩
  · intro i x
    have e := gate_eq gates x i.val i.isLt (hord i)
    have hfun : (fun k => (W gates x).getD k false) = fun k => ev k x :=
      funext (fun k => (E k x).symm)
    rw [hfun, ← E] at e
    exact e
  · intro k hk x
    rw [E]
    exact List.getD_eq_default _ _ (by rw [W_len]; omega)

private lemma two_list (l : List ℕ) (a b : ℕ) (hl : l.length ≤ 2) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ k ∈ l, k = a ∨ k = b := by
  match l, hl, ha, hb with
  | [], _, ha, _ => exact absurd ha List.not_mem_nil
  | [x], _, ha, hb =>
    exfalso
    simp at ha hb
    omega
  | [x, y], _, ha, hb =>
    intro k hk
    simp at ha hb hk
    omega
  | _ :: _ :: _ :: _, hl, _, _ =>
    exfalso
    simp only [List.length_cons] at hl
    omega

private lemma two_cover (l : List ℕ) (hl : l.length ≤ 2) (hne : l ≠ []) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ ∀ k ∈ l, k = a ∨ k = b := by
  match l, hl, hne with
  | [], _, hne => exact absurd rfl hne
  | [x], _, _ => exact ⟨x, x, by simp, by simp, by simp⟩
  | [x, y], _, _ => exact ⟨x, y, by simp, by simp, by simp⟩
  | _ :: _ :: _ :: _, hl, _ =>
    exfalso
    simp only [List.length_cons] at hl
    omega

private lemma count_fin {n : ℕ} (U R : Finset (Fin n)) (j : Fin n) (hj : j ∉ R)
    (hU : ∀ g ∈ U, g ≠ j ∧ g ∉ R) : U.card + R.card + 1 ≤ n := by
  have hd : Disjoint U (insert j R) := by
    refine Finset.disjoint_left.mpr (fun g hg hg2 => ?_)
    rcases Finset.mem_insert.mp hg2 with e | e
    · exact (hU g hg).1 e
    · exact (hU g hg).2 e
  have h1 := Finset.card_union_of_disjoint hd
  have h2 := Finset.card_le_card (Finset.subset_univ (U ∪ insert j R))
  rw [Finset.card_univ, Fintype.card_fin, h1, Finset.card_insert_of_notMem hj] at h2
  omega

private lemma descent {N : ℕ} (S : ℕ → Prop) (cov : ℕ → Finset (Fin N)) (X : Finset ℕ)
    (hstep : ∀ w, S w →
      (cov w).card ≤ 1 ∨
      (∃ e, e < w ∧ S e ∧ cov w ⊆ cov e) ∨
      (w ∈ X ∧ ∃ e1 e2, e1 < w ∧ e2 < w ∧ S e1 ∧ S e2 ∧ cov w ⊆ cov e1 ∪ cov e2) ∨
      (w ∈ X ∧ ∃ e, e < w ∧ S e ∧ ∃ v, cov w ⊆ insert v (cov e))) :
    ∀ (n : ℕ) (F : Finset ℕ), (∀ w ∈ F, S w ∧ w < n) →
      (F.biUnion cov).card ≤ F.card + (X.filter (fun w => w < n)).card := by
  intro n
  induction n with
  | zero =>
    intro F hF
    have hF0 : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      exact absurd (hF w hw).2 (Nat.not_lt_zero w)
    rw [hF0]
    simp
  | succ n ih =>
    intro F hF
    have hmono : (X.filter (fun w => w < n)).card ≤ (X.filter (fun w => w < n + 1)).card :=
      Finset.card_le_card (fun w hw => by
        have h1 := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨h1.1, by omega⟩)
    have hXc : n ∈ X →
        (X.filter (fun w => w < n)).card + 1 ≤ (X.filter (fun w => w < n + 1)).card := by
      intro hX
      have hsub : insert n (X.filter (fun w => w < n)) ⊆ X.filter (fun w => w < n + 1) := by
        intro w hw
        rcases Finset.mem_insert.mp hw with e | hw
        · rw [e]
          exact Finset.mem_filter.mpr ⟨hX, Nat.lt_succ_self _⟩
        · have h1 := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨h1.1, by omega⟩
      have hnot : n ∉ X.filter (fun w => w < n) := by
        intro hmem
        exact lt_irrefl n (Finset.mem_filter.mp hmem).2
      have h2 := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at h2
      exact h2
    by_cases hn : n ∈ F
    · have hF0 : ∀ w ∈ F.erase n, S w ∧ w < n := by
        intro w hw
        have h1 := Finset.mem_erase.mp hw
        have h2 := hF w h1.2
        have h3 := h1.1
        exact ⟨h2.1, by omega⟩
      have hcardF : (F.erase n).card + 1 = F.card := Finset.card_erase_add_one hn
      have hbU : F.biUnion cov = cov n ∪ (F.erase n).biUnion cov := by
        rw [← Finset.biUnion_insert, Finset.insert_erase hn]
      have h0 := ih (F.erase n) hF0
      rcases hstep n (hF n hn).1 with hleaf | ⟨e, hen, hSe, hsub⟩ |
        ⟨hX, e1, e2, h1, h2, hS1, hS2, hsub⟩ | ⟨hX, e, hen, hSe, v, hsub⟩
      · have h4 := Finset.card_union_le (cov n) ((F.erase n).biUnion cov)
        rw [hbU]
        omega
      · have hF2 : ∀ w ∈ insert e (F.erase n), S w ∧ w < n := by
          intro w hw
          rcases Finset.mem_insert.mp hw with e3 | hw
          · rw [e3]
            exact ⟨hSe, hen⟩
          · exact hF0 w hw
        have h3 := ih _ hF2
        have h4 : F.biUnion cov ⊆ (insert e (F.erase n)).biUnion cov := by
          rw [hbU, Finset.biUnion_insert]
          exact Finset.union_subset_union hsub (Finset.Subset.refl _)
        have h5 := Finset.card_le_card h4
        have h6 := Finset.card_insert_le e (F.erase n)
        omega
      · have hF2 : ∀ w ∈ insert e1 (insert e2 (F.erase n)), S w ∧ w < n := by
          intro w hw
          rcases Finset.mem_insert.mp hw with e3 | hw
          · rw [e3]
            exact ⟨hS1, h1⟩
          · rcases Finset.mem_insert.mp hw with e3 | hw
            · rw [e3]
              exact ⟨hS2, h2⟩
            · exact hF0 w hw
        have h3 := ih _ hF2
        have h4 : F.biUnion cov ⊆ (insert e1 (insert e2 (F.erase n))).biUnion cov := by
          rw [hbU, Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
          exact Finset.union_subset_union hsub (Finset.Subset.refl _)
        have h5 := Finset.card_le_card h4
        have h6 := Finset.card_insert_le e1 (insert e2 (F.erase n))
        have h7 := Finset.card_insert_le e2 (F.erase n)
        have h8 := hXc hX
        omega
      · have hF2 : ∀ w ∈ insert e (F.erase n), S w ∧ w < n := by
          intro w hw
          rcases Finset.mem_insert.mp hw with e3 | hw
          · rw [e3]
            exact ⟨hSe, hen⟩
          · exact hF0 w hw
        have h3 := ih _ hF2
        have h4 : F.biUnion cov ⊆ insert v ((insert e (F.erase n)).biUnion cov) := by
          rw [hbU, Finset.biUnion_insert]
          intro u hu
          rcases Finset.mem_union.mp hu with hu | hu
          · rcases Finset.mem_insert.mp (hsub hu) with e3 | hu2
            · rw [e3]
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hu2)
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hu)
        have h5 := Finset.card_le_card h4
        have h6 := Finset.card_insert_le e (F.erase n)
        have h7 := Finset.card_insert_le v ((insert e (F.erase n)).biUnion cov)
        have h8 := hXc hX
        omega
    · have hF0 : ∀ w ∈ F, S w ∧ w < n := by
        intro w hw
        have h2 := hF w hw
        have h3 : w ≠ n := fun e => hn (e ▸ hw)
        exact ⟨h2.1, by omega⟩
      have h0 := ih F hF0
      omega

private lemma line_count {q N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hcard : ∀ i : Fin N, (L i).card = q + 1)
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hm0 : p0 ∈ L i0) (hm1 : p1 ∈ L i0)
    (gates : List Gate) (j : Fin gates.length) (ev : ℕ → (Fin N → Bool) → Bool)
    (F_in : ∀ (k : ℕ) (hk : k < N) (x : Fin N → Bool), ev k x = x ⟨k, hk⟩)
    (F_gate : ∀ (i : Fin gates.length) (x : Fin N → Bool),
      ev (N + (i : ℕ)) x = (gates.get i).op.eval ((gates.get i).inputs.map fun k => ev k x))
    (F_out : ∀ (k : ℕ), N + gates.length ≤ k → ∀ x : Fin N → Bool, ev k x = false)
    (hord : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ))
    (hop : ∀ i : Fin gates.length, i ≠ j →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or)
    (hlen : ∀ i : Fin gates.length, (gates.get i).inputs.length ≤ 2)
    (Z1 : ∀ v : Fin N, v ≠ p0 → v ≠ p1 → ev (N + (j : ℕ)) (fun u : Fin N => decide (u = v)) = true)
    (Z00 : ev (N + (j : ℕ)) (fun u : Fin N => decide (u = p0)) = false)
    (Z01 : ev (N + (j : ℕ)) (fun u : Fin N => decide (u = p1)) = false)
    (Zempty : ev (N + (j : ℕ)) (fun _ : Fin N => false) = true)
    (t : Fin N) (S : ℕ → Prop)
    (hS0 : ∀ w, S w → ev w (fun _ : Fin N => false) = false)
    (C2 : ∀ (w : ℕ) (v : Fin N), S w → v ∉ L i0 →
      ev w (fun u : Fin N => decide (u = v)) = true → v ∈ L t)
    (C3 : ∀ g : Fin gates.length, (gates.get g).op = GateOp.or → S (N + (g : ℕ)) →
      ∀ e ∈ (gates.get g).inputs, S e)
    (C4 : ∀ g : Fin gates.length, (gates.get g).op = GateOp.and → S (N + (g : ℕ)) →
      ∃ e ∈ (gates.get g).inputs, S e)
    (ot : ℕ) (hSo : S ot)
    (hot : ∀ v : Fin N, ev ot (fun u : Fin N => decide (u = v)) = true ↔ v ∈ L t)
    (Gd : ℕ → Prop)
    (hGd : ∀ w, Gd w ↔ ((∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true → v ∈ L t) ∨
      (p0 ∉ L t ∧ p1 ∉ L t ∧ ∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true →
        v ∈ L t ∨ v = p0 ∨ v = p1)))
    (cv : ℕ → Finset (Fin N))
    (hcv : ∀ (w : ℕ) (v : Fin N), v ∈ cv w ↔ (ev w (fun u : Fin N => decide (u = v)) = true ∧
      (v ∉ L i0 ∨ (v ∈ L t ∧ Gd w))))
    (A : Finset (Fin gates.length))
    (hA : ∀ g : Fin gates.length, g ∈ A ↔ (g ≠ j ∧ N + (j : ℕ) ∉ (gates.get g).inputs ∧
      S (N + (g : ℕ)) ∧ 2 ≤ (cv (N + (g : ℕ))).card)) :
    q ≤ A.card := by
  have hSz : ¬ S (N + (j : ℕ)) := by
    intro hS
    have h1 := hS0 _ hS
    rw [Zempty] at h1
    exact Bool.noConfusion h1
  have hstep : ∀ w, S w →
      (cv w).card ≤ 1 ∨
      (∃ e, e < w ∧ S e ∧ cv w ⊆ cv e) ∨
      (w ∈ A.image (fun g : Fin gates.length => N + (g : ℕ)) ∧
        ∃ e1 e2, e1 < w ∧ e2 < w ∧ S e1 ∧ S e2 ∧ cv w ⊆ cv e1 ∪ cv e2) ∨
      (w ∈ A.image (fun g : Fin gates.length => N + (g : ℕ)) ∧
        ∃ e, e < w ∧ S e ∧ ∃ v, cv w ⊆ insert v (cv e)) := by
    intro w hSw
    by_cases hc : (cv w).card ≤ 1
    · exact Or.inl hc
    by_cases h1 : w < N
    · exfalso
      have hsub : cv w ⊆ {(⟨w, h1⟩ : Fin N)} := by
        intro v hv
        have h2 := ((hcv w v).mp hv).1
        rw [F_in w h1] at h2
        have h3 : (⟨w, h1⟩ : Fin N) = v := of_decide_eq_true h2
        rw [Finset.mem_singleton]
        exact h3.symm
      have h4 := Finset.card_le_card hsub
      rw [Finset.card_singleton] at h4
      exact hc h4
    by_cases h2 : w < N + gates.length
    swap
    · exfalso
      have hemp : cv w = ∅ := Finset.eq_empty_of_forall_notMem (fun v hv => by
        have h3 := ((hcv w v).mp hv).1
        rw [F_out w (by omega)] at h3
        exact Bool.noConfusion h3)
      rw [hemp] at hc
      exact hc (by simp)
    obtain ⟨g, hwg⟩ : ∃ g : Fin gates.length, w = N + (g : ℕ) :=
      ⟨⟨w - N, by omega⟩, by show w = N + (w - N); omega⟩
    subst hwg
    have hgj : g ≠ j := by
      intro e
      rw [e] at hSw
      exact hSz hSw
    have hlg := hlen g
    rcases hop g hgj with hand | hor
    · obtain ⟨e, he, hSe⟩ := C4 g hand hSw
      have helt := hord g e he
      have hall : ∀ x : Fin N → Bool, ev (N + (g : ℕ)) x = true →
          ∀ k ∈ (gates.get g).inputs, ev k x = true := by
        intro x hx
        rw [F_gate g x, hand] at hx
        exact (all_true _ _).mp hx
      have hall2 : ∀ x : Fin N → Bool, (∀ k ∈ (gates.get g).inputs, ev k x = true) →
          ev (N + (g : ℕ)) x = true := by
        intro x hx
        rw [F_gate g x, hand]
        exact (all_true _ _).mpr hx
      by_cases hr : N + (j : ℕ) ∈ (gates.get g).inputs
      · right
        left
        refine ⟨e, helt, hSe, ?_⟩
        have hez : N + (j : ℕ) ≠ e := by
          intro e1
          rw [← e1] at hSe
          exact hSz hSe
        have hin := two_list _ _ _ hlg hr he hez
        intro v hv
        obtain ⟨hv1, hv2⟩ := (hcv _ v).mp hv
        have hev1 := hall _ hv1 e he
        have hzv := hall _ hv1 _ hr
        refine (hcv e v).mpr ⟨hev1, ?_⟩
        rcases hv2 with hv2 | ⟨hvt, hG⟩
        · exact Or.inl hv2
        · by_cases hvi : v ∈ L i0
          swap
          · exact Or.inl hvi
          right
          refine ⟨hvt, ?_⟩
          have hv0 : v ≠ p0 := by
            intro e1
            rw [e1, Z00] at hzv
            exact Bool.noConfusion hzv
          have hv1b : v ≠ p1 := by
            intro e1
            rw [e1, Z01] at hzv
            exact Bool.noConfusion hzv
          have hsup : ∀ u : Fin N, ev e (fun u2 : Fin N => decide (u2 = u)) = true →
              u = p0 ∨ u = p1 ∨ ev (N + (g : ℕ)) (fun u2 : Fin N => decide (u2 = u)) = true := by
            intro u hu
            by_cases hu0 : u = p0
            · exact Or.inl hu0
            by_cases hu1 : u = p1
            · exact Or.inr (Or.inl hu1)
            right
            right
            apply hall2
            intro k hk
            rcases hin k hk with e1 | e1
            · rw [e1]
              exact Z1 u hu0 hu1
            · rw [e1]
              exact hu
          rw [hGd]
          by_cases ht : t = i0
          · left
            intro u hu
            rcases hsup u hu with r | r | r
            · rw [r, ht]
              exact hm0
            · rw [r, ht]
              exact hm1
            · rcases (hGd _).mp hG with hD | ⟨hp0, _, _⟩
              · exact hD u r
              · exact absurd (by rw [ht]; exact hm0) hp0
          · have hone := hint t i0 ht
            have hnp : ∀ p : Fin N, p ∈ L i0 → p ≠ v → p ∉ L t := by
              intro p hp hpv hpt
              have hsub : ({p, v} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
                intro a ha
                rcases Finset.mem_insert.mp ha with e1 | ha
                · rw [e1]
                  exact Finset.mem_inter.mpr ⟨hpt, hp⟩
                · rw [Finset.mem_singleton] at ha
                  rw [ha]
                  exact Finset.mem_inter.mpr ⟨hvt, hvi⟩
              have h5 := Finset.card_le_card hsub
              rw [Finset.card_pair_eq_two_iff.mpr hpv, hone] at h5
              omega
            right
            refine ⟨hnp p0 hm0 (Ne.symm hv0), hnp p1 hm1 (Ne.symm hv1b), ?_⟩
            intro u hu
            rcases hsup u hu with r | r | r
            · exact Or.inr (Or.inl r)
            · exact Or.inr (Or.inr r)
            · rcases (hGd _).mp hG with hD | ⟨_, _, hP⟩
              · exact Or.inl (hD u r)
              · exact hP u r
      · have hgA : g ∈ A := (hA g).mpr ⟨hgj, hr, hSw, by omega⟩
        have hX : N + (g : ℕ) ∈ A.image (fun g : Fin gates.length => N + (g : ℕ)) :=
          Finset.mem_image.mpr ⟨g, hgA, rfl⟩
        by_cases ht : t = i0
        · right
          left
          refine ⟨e, helt, hSe, ?_⟩
          intro v hv
          obtain ⟨hv1, hv2⟩ := (hcv _ v).mp hv
          have hev1 := hall _ hv1 e he
          refine (hcv e v).mpr ⟨hev1, ?_⟩
          rcases hv2 with hv2 | ⟨hvt, _⟩
          · exact Or.inl hv2
          · right
            refine ⟨hvt, (hGd e).mpr (Or.inl ?_)⟩
            intro u hu
            by_contra hut
            have hui : u ∉ L i0 := by
              rw [← ht]
              exact hut
            exact hut (C2 e u hSe hui hu)
        · right
          right
          right
          obtain ⟨m, hm⟩ := Finset.card_eq_one.mp (hint t i0 ht)
          refine ⟨hX, e, helt, hSe, m, ?_⟩
          intro v hv
          obtain ⟨hv1, hv2⟩ := (hcv _ v).mp hv
          have hev1 := hall _ hv1 e he
          by_cases hvi : v ∈ L i0
          · have hvt : v ∈ L t := by
              rcases hv2 with hv2 | ⟨hvt, _⟩
              · exact absurd hvi hv2
              · exact hvt
            have h5 : v ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hvt, hvi⟩
            rw [hm, Finset.mem_singleton] at h5
            rw [h5]
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem ((hcv e v).mpr ⟨hev1, Or.inl hvi⟩)
    · have hany : ∀ x : Fin N → Bool, ev (N + (g : ℕ)) x = true →
          ∃ k ∈ (gates.get g).inputs, ev k x = true := by
        intro x hx
        rw [F_gate g x, hor] at hx
        exact (any_true _ _).mp hx
      have hany2 : ∀ (x : Fin N → Bool) (k : ℕ), k ∈ (gates.get g).inputs → ev k x = true →
          ev (N + (g : ℕ)) x = true := by
        intro x k hk hkx
        rw [F_gate g x, hor]
        exact (any_true _ _).mpr ⟨k, hk, hkx⟩
      have hr : N + (j : ℕ) ∉ (gates.get g).inputs := by
        intro hr
        have h3 := hS0 _ hSw
        rw [hany2 _ _ hr Zempty] at h3
        exact Bool.noConfusion h3
      have hgA : g ∈ A := (hA g).mpr ⟨hgj, hr, hSw, by omega⟩
      have hX : N + (g : ℕ) ∈ A.image (fun g : Fin gates.length => N + (g : ℕ)) :=
        Finset.mem_image.mpr ⟨g, hgA, rfl⟩
      have hne : (gates.get g).inputs ≠ [] := by
        intro hnil
        have hemp : cv (N + (g : ℕ)) = ∅ := Finset.eq_empty_of_forall_notMem (fun v hv => by
          obtain ⟨k, hk, _⟩ := hany _ ((hcv _ v).mp hv).1
          rw [hnil] at hk
          exact absurd hk List.not_mem_nil)
        rw [hemp] at hc
        exact hc (by simp)
      obtain ⟨a, b, ha, hb, hab⟩ := two_cover _ hlg hne
      right
      right
      left
      refine ⟨hX, a, b, hord g a ha, hord g b hb, C3 g hor hSw a ha, C3 g hor hSw b hb, ?_⟩
      intro v hv
      obtain ⟨hv1, hv2⟩ := (hcv _ v).mp hv
      obtain ⟨k, hk, hkv⟩ := hany _ hv1
      have hkc : v ∈ cv k := by
        refine (hcv k v).mpr ⟨hkv, ?_⟩
        rcases hv2 with hv2 | ⟨hvt, hG⟩
        · exact Or.inl hv2
        · right
          refine ⟨hvt, (hGd k).mpr ?_⟩
          rcases (hGd _).mp hG with hD | ⟨h0, h1b, hP⟩
          · exact Or.inl (fun u hu => hD u (hany2 _ k hk hu))
          · exact Or.inr ⟨h0, h1b, fun u hu => hP u (hany2 _ k hk hu)⟩
      rcases hab k hk with e1 | e1
      · rw [e1] at hkc
        exact Finset.mem_union_left _ hkc
      · rw [e1] at hkc
        exact Finset.mem_union_right _ hkc
  have hd := descent S cv (A.image (fun g : Fin gates.length => N + (g : ℕ))) hstep (ot + 1) {ot}
    (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      exact ⟨hSo, Nat.lt_succ_self _⟩)
  rw [Finset.singleton_biUnion, Finset.card_singleton] at hd
  have hcvo : cv ot = L t := by
    ext v
    rw [hcv]
    constructor
    · intro hh
      exact (hot v).mp hh.1
    · intro hv
      refine ⟨(hot v).mpr hv, ?_⟩
      by_cases hvi : v ∈ L i0
      · exact Or.inr ⟨hv, (hGd ot).mpr (Or.inl (fun u hu => (hot u).mp hu))⟩
      · exact Or.inl hvi
  rw [hcvo, hcard t] at hd
  have h3 : ((A.image (fun g : Fin gates.length => N + (g : ℕ))).filter
      (fun w => w < ot + 1)).card ≤ (A.image (fun g : Fin gates.length => N + (g : ℕ))).card :=
    Finset.card_filter_le _ _
  have h4 : (A.image (fun g : Fin gates.length => N + (g : ℕ))).card ≤ A.card :=
    Finset.card_image_le
  omega

theorem main_aux : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    (∀ p : Fin N, p ≠ p0 → p ≠ p1 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = false) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o j h hg hord hjnot hjuniq hhj
    hjin hout hh0 hh1 hhp hhW
  classical
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → (Fin N → Bool) → Bool, ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) :=
    ⟨fun w x => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x),
      fun _ _ => rfl⟩
  have hh0b : ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true := (hev _ _).trans hh0
  have hh1b : ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true := (hev _ _).trans hh1
  have hhpb : ∀ p : Fin N, p ≠ p0 → p ≠ p1 →
      ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false :=
    fun p a b => (hev _ _).trans (hhp p a b)
  have hhWb : ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false :=
    (hev _ _).trans hhW
  obtain ⟨P1, P2, Pz0, Pz1, -⟩ := base q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o
    j h hg hord hjnot hjuniq hhj hjin hout ev hev hh0b hh1b hhpb hhWb
  obtain ⟨Sm, hSm⟩ : ∃ Sm : Fin N → ℕ → Prop, ∀ (t : Fin N) (w : ℕ), Sm t w ↔
      ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true →
        ∃ v ∈ L t, x v = true :=
    ⟨fun t w => ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true →
        ∃ v ∈ L t, x v = true, fun _ _ => Iff.rfl⟩
  obtain ⟨Dm, hDm⟩ : ∃ Dm : Fin N → ℕ → Prop, ∀ (t : Fin N) (w : ℕ), Dm t w ↔
      (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t) :=
    ⟨fun t w => (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t),
      fun _ _ => Iff.rfl⟩
  obtain ⟨Vs, hVs⟩ : ∃ Vs : Fin N → ℕ → Fin N → Prop, ∀ (t : Fin N) (w : ℕ) (v : Fin N),
      Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨
        (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true)) :=
    ⟨fun t w v => ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨
        (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true)),
      fun _ _ _ => Iff.rfl⟩
  have hB := fun t : Fin N => cellB q N L i0 p0 p1 hq hN hcard hint hjoin hne hm0 hm1 gates o
    j h hg hord hjnot hjuniq hhj hjin hout ev hev hh0b hh1b hhpb hhWb Sm Dm hSm hDm Vs hVs t
  obtain ⟨F_in, F_gate, F_out⟩ := facts gates hord ev hev
  have hop : ∀ i : Fin gates.length, i ≠ j →
      (gates.get i).op = GateOp.and ∨ (gates.get i).op = GateOp.or := by
    intro i hij
    rcases (hg (gates.get i) (List.get_mem gates i)).1 with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact absurd (hjuniq i a) hij
  have hlen : ∀ i : Fin gates.length, (gates.get i).inputs.length ≤ 2 :=
    fun i => (hg (gates.get i) (List.get_mem gates i)).2
  have Z1 : ∀ v : Fin N, v ≠ p0 → v ≠ p1 →
      ev (N + (j : ℕ)) (fun u : Fin N => decide (u = v)) = true := by
    intro v h0 h1
    by_cases hv : v ∈ L i0
    · exact (P2 v hv h0 h1).2
    · refine (P1 _ (fun u hu => ?_)).2
      have hu2 : u = v := of_decide_eq_true hu
      rw [hu2]
      exact hv
  have Zempty : ev (N + (j : ℕ)) (fun _ : Fin N => false) = true :=
    (P1 _ (fun v hv => Bool.noConfusion hv)).2
  have hS0 : ∀ (t : Fin N) (w : ℕ), Sm t w → ev w (fun _ : Fin N => false) = false := by
    intro t w hS
    apply Bool.eq_false_iff.mpr
    intro hcase
    obtain ⟨v, _, hv⟩ := (hSm t w).mp hS _ (fun v hv => Bool.noConfusion hv) hcase
    exact Bool.noConfusion hv
  have hSo : ∀ t : Fin N, Sm t (o t) := by
    intro t
    refine (hSm t (o t)).mpr (fun x _ he => ?_)
    rw [hev, hout t x] at he
    exact of_decide_eq_true he
  have hot : ∀ (t v : Fin N), ev (o t) (fun u : Fin N => decide (u = v)) = true ↔ v ∈ L t := by
    intro t v
    rw [hev, hout]
    constructor
    · intro hh
      obtain ⟨u, hu, hu2⟩ := of_decide_eq_true hh
      have hu3 : u = v := of_decide_eq_true hu2
      rw [← hu3]
      exact hu
    · intro hv
      exact decide_eq_true ⟨v, hv, decide_eq_true rfl⟩
  obtain ⟨Gd, hGd⟩ : ∃ Gd : Fin N → ℕ → Prop, ∀ (t : Fin N) (w : ℕ), Gd t w ↔
      ((∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true → v ∈ L t) ∨
      (p0 ∉ L t ∧ p1 ∉ L t ∧ ∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true →
        v ∈ L t ∨ v = p0 ∨ v = p1)) :=
    ⟨fun t w => ((∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true → v ∈ L t) ∨
      (p0 ∉ L t ∧ p1 ∉ L t ∧ ∀ v : Fin N, ev w (fun u : Fin N => decide (u = v)) = true →
        v ∈ L t ∨ v = p0 ∨ v = p1)), fun _ _ => Iff.rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ cv : Fin N → ℕ → Finset (Fin N), ∀ (t : Fin N) (w : ℕ) (v : Fin N),
      v ∈ cv t w ↔ (ev w (fun u : Fin N => decide (u = v)) = true ∧
        (v ∉ L i0 ∨ (v ∈ L t ∧ Gd t w))) :=
    ⟨fun t w => Finset.univ.filter (fun v : Fin N =>
        ev w (fun u : Fin N => decide (u = v)) = true ∧ (v ∉ L i0 ∨ (v ∈ L t ∧ Gd t w))),
      fun t w v => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin N → Finset (Fin gates.length), ∀ (t : Fin N)
      (g : Fin gates.length), g ∈ A t ↔ (g ≠ j ∧ N + (j : ℕ) ∉ (gates.get g).inputs ∧
        Sm t (N + (g : ℕ)) ∧ 2 ≤ (cv t (N + (g : ℕ))).card) :=
    ⟨fun t => Finset.univ.filter (fun g : Fin gates.length =>
        g ≠ j ∧ N + (j : ℕ) ∉ (gates.get g).inputs ∧
        Sm t (N + (g : ℕ)) ∧ 2 ≤ (cv t (N + (g : ℕ))).card),
      fun t g => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]⟩
  have hline : ∀ t : Fin N, q ≤ (A t).card := fun t =>
    line_count L i0 p0 p1 hcard hint hm0 hm1 gates j ev F_in F_gate F_out hord hop hlen Z1 Pz0 Pz1
      Zempty t (Sm t) (hS0 t) (hB t).2.1 (fun g hor hS => ((hB t).2.2.1 g hor).1 hS)
      (hB t).2.2.2.1 (o t) (hSo t) (hot t) (Gd t) (hGd t) (cv t) (hcv t) (A t) (hA t)
  have hcvL : ∀ (s : Fin N) (w : ℕ), Sm s w → cv s w ⊆ L s := by
    intro s w hS v hv
    obtain ⟨hv1, hv2⟩ := (hcv s w v).mp hv
    rcases hv2 with hv2 | ⟨hvs, _⟩
    · exact (hB s).2.1 w v hS hv2 hv1
    · exact hvs
  have hdisj : ∀ t t2 : Fin N, t ≠ t2 → Disjoint (A t) (A t2) := by
    intro t t2 htt
    rw [Finset.disjoint_left]
    intro g hg hg2
    obtain ⟨_, _, hS, hc⟩ := (hA t g).mp hg
    obtain ⟨_, _, hS2, hc2⟩ := (hA t2 g).mp hg2
    have key : ∀ T : Finset (Fin N), 2 ≤ T.card → T ⊆ L t → T ⊆ L t2 → False := by
      intro T hT h1 h2
      have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
      rw [hint t t2 htt] at h3
      omega
    by_cases hG : Gd t (N + (g : ℕ))
    · by_cases hG2 : Gd t2 (N + (g : ℕ))
      · rcases (hGd t _).mp hG with hD | ⟨h0, h1, hP⟩
        · exact key (cv t2 (N + (g : ℕ))) hc2 (fun v hv => hD v ((hcv t2 _ v).mp hv).1)
            (hcvL t2 _ hS2)
        · rcases (hGd t2 _).mp hG2 with hD2 | ⟨_, _, hP2⟩
          · exact key (cv t (N + (g : ℕ))) hc (hcvL t _ hS)
              (fun v hv => hD2 v ((hcv t _ v).mp hv).1)
          · refine key (cv t (N + (g : ℕ))) hc (hcvL t _ hS) (fun v hv => ?_)
            have hvt := hcvL t _ hS hv
            rcases hP2 v ((hcv t _ v).mp hv).1 with r | r | r
            · exact r
            · rw [r] at hvt
              exact absurd hvt h0
            · rw [r] at hvt
              exact absurd hvt h1
      · refine key (cv t2 (N + (g : ℕ))) hc2 (fun v hv => ?_) (hcvL t2 _ hS2)
        obtain ⟨hv1, hv2⟩ := (hcv t2 _ v).mp hv
        rcases hv2 with hv2 | ⟨_, hGG⟩
        · exact (hB t).2.1 _ v hS hv2 hv1
        · exact absurd hGG hG2
    · refine key (cv t (N + (g : ℕ))) hc (hcvL t _ hS) (fun v hv => ?_)
      obtain ⟨hv1, hv2⟩ := (hcv t _ v).mp hv
      rcases hv2 with hv2 | ⟨_, hGG⟩
      · exact (hB t2).2.1 _ v hS2 hv2 hv1
      · exact absurd hGG hG
  have hsum : N * q ≤ ((Finset.univ : Finset (Fin N)).biUnion A).card := by
    rw [Finset.card_biUnion (fun t _ t2 _ htt => hdisj t t2 htt)]
    calc N * q = ∑ _t : Fin N, q := by simp
      _ ≤ ∑ t : Fin N, (A t).card := Finset.sum_le_sum (fun t _ => hline t)
  refine Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _)
    (count_fin _ _ j ?_ ?_)
  · intro hj
    have h1 := (Finset.mem_filter.mp hj).2
    exact absurd (hord j _ h1) (lt_irrefl _)
  · intro g hg
    obtain ⟨t, _, hgt⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨h1, h2, _, _⟩ := (hA t g).mp hgt
    exact ⟨h1, fun hm => h2 (Finset.mem_filter.mp hm).2⟩

end PEqualNP.Outside.L_meta_1648

theorem PEqualNP.Outside.L_meta_1648 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p0))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p1))) = true →
    (∀ p : Fin N, p ≠ p0 → p ≠ p1 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = false) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, (N + (h : ℕ))⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1648.main_aux
