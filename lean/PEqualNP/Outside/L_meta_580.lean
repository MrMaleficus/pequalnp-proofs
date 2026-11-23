import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PathGateReduction

-- The constant-propagation pass follows L_meta_468.

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

private lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

private lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

end PathGateReduction
namespace Path574
open PEqualNP.MetaComplexity

private abbrev indep {m : ℕ} (F : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∀ x b, F (Function.update x p b) = F x

private abbrev varies {m : ℕ} (F : (Fin m → Bool) → Bool) : Prop := ∃ x y, F x ≠ F y

private theorem peel_one {m s : ℕ} (B : (Fin m → Bool) → Bool) (p q : Fin m) (hpq : p ≠ q)
    (safe : indep B p) (variesB : varies B) (possible : ∃ x, B x = false ∧ x q = true)
    (size : HasCircuitSize m (fun x => B x || (x p && x q)) s) :
    ∃ a, a+1 ≤ s ∧ HasCircuitSize m B a := by
  let F (x : Fin m → Bool) := B x || (x p && x q)
  have off (x : Fin m → Bool) : F (Function.update x p false) = B x := by simp [F,safe]
  have on (x : Fin m → Bool) : F (Function.update x p true) = (B x || x q) := by
    simp [F, safe, Function.update_of_ne hpq.symm]
  obtain ⟨x,hx,hq⟩ := possible
  obtain ⟨a,b,hab⟩ := variesB
  have ⟨h,hs⟩ := PathGateReduction.elim_one_var (F:=F) p false size
    ⟨x,by simp [off,on,hx,hq]⟩ ⟨a,b,by simpa only [off] using hab⟩
  exact ⟨s-1,by omega,by simpa only [off] using hs⟩

private theorem peel_two {m s : ℕ} (B : (Fin m → Bool) → Bool) (p q t : Fin m)
    (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) (bp : indep B p) (bq : indep B q)
    (vb : varies B) (possible : ∃ x, B x = false ∧ x t = false)
    (size : HasCircuitSize m (fun x => B x || (x q && (x t || x p))) s) :
    (∃ a, a+2 ≤ s ∧ HasCircuitSize m (fun x => B x || (x q && x t)) a) ∨
    (∃ a, a+3 ≤ s ∧ HasCircuitSize m B a) := by
  let F (x : Fin m → Bool) := B x || (x q && (x t || x p))
  let J (x : Fin m → Bool) := B x || x q
  have off (x : Fin m → Bool) : F (Function.update x p false) = (B x || (x q && x t)) := by
    simp [F,bp,Function.update_of_ne hpq.symm,Function.update_of_ne hpt.symm]
  have on (x : Fin m → Bool) : F (Function.update x p true) = J x := by
    simp [F,J,bp,Function.update_of_ne hpq.symm]
  have zero (x : Fin m → Bool) : J (Function.update x q false) = B x := by simp [J,bq]
  have atzero (x : Fin m → Bool) :
      F (Function.update (Function.update x q false) p false) = B x := by simp [off,bq]
  obtain ⟨x,hx,ht⟩ := possible
  obtain ⟨a,b,hab⟩ := vb
  have hdep : ∃ y, F (Function.update y p false) ≠ F (Function.update y p true) := by
    refine ⟨Function.update x q true,?_⟩
    simp [off,on,J,bq,hx,Function.update_of_ne hqt.symm,ht]
  obtain ⟨hsz,hs | hs⟩ := PathGateReduction.elim_two_var (F:=F) p size hdep
    ⟨Function.update a q false, Function.update b q false, by simpa only [atzero] using hab⟩
    ⟨Function.update a q false, Function.update b q false, by simpa only [on,zero] using hab⟩
  · exact Or.inl ⟨s-2,by omega,by simpa only [off] using hs⟩
  · have hj : HasCircuitSize m J (s-2) := by simpa only [on] using hs
    have hdepJ : ∃ y, J (Function.update y q false) ≠ J (Function.update y q true) :=
      ⟨x,by simp [J,bq,hx]⟩
    obtain ⟨h,hd⟩ := PathGateReduction.elim_one_var (F:=J) q false hj hdepJ ⟨a,b,by simpa only [zero] using hab⟩
    exact Or.inr ⟨s-2-1,by omega,by simpa only [zero] using hd⟩

end Path574

namespace Path574
open PEqualNP.MetaComplexity

private theorem remove_bare {m s : ℕ} (F : (Fin m → Bool) → Bool) (a : Fin m)
    (hu : ∀ x b, F (Function.update x a b) = F x) (hn : ∃ x y, F x ≠ F y)
    (hc : HasCircuitSize m (fun x => F x || x a) s) : 1 ≤ s ∧ HasCircuitSize m F (s-1) := by
  obtain ⟨x,y,hd⟩ := hn
  obtain ⟨z,hz⟩ : ∃ z, F z = false := by
    cases hx : F x <;> cases hy : F y <;> simp_all <;> aesop
  have h1 := PathGateReduction.elim_one_var a false hc ⟨z, by simp [hu,hz]⟩
    ⟨x,y,by simpa [hu] using hd⟩
  simpa only [hu,Function.update_self,Bool.or_false] using h1


end Path574

namespace Peel580
open PEqualNP.MetaComplexity

private noncomputable def Fn {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _) || g x

private def Concl {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (bu bv : Bool) (T : Finset (Fin n)) (s' : ℕ), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧
    (pv 0 ∈ T ↔ bu = true) ∧ (pv (m + 1) ∈ T ↔ bv = true) ∧
    HasCircuitSize n (fun x : Fin n → Bool => g x || (bu && x (pv 0) && x (pv 1)) ||
      (bv && x (pv m) && x (pv (m + 1)))) s' ∧
    A.card + G.edgeSet.ncard + T.card +
      ((if bu = true then 0 else 2) + (if bv = true then 0 else 2)) + s' ≤ s + 4

private def Sub {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n, G.Adj i j →
    ∃ k : ℕ, k ≤ m ∧ ((pv k = i ∧ pv (k + 1) = j) ∨ (pv k = j ∧ pv (k + 1) = i))

private def Win {n : ℕ} (pv : ℕ → Fin n) (G : SimpleGraph (Fin n)) (a b : ℕ) : Prop :=
  ∀ k : ℕ, a ≤ k → k ≤ b → ¬ G.Adj (pv k) (pv (k + 1))

private def Touch {n : ℕ} (W : Finset (Fin n)) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n, G.Adj i j → i ∈ W ∨ j ∈ W

private def Ign {n : ℕ} (W : Finset (Fin n)) (g : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i : Fin n, i ∉ W → x i = y i) → g x = g y

private def zeroW {n : ℕ} (W : Finset (Fin n)) (z : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ W then false else z i

private lemma Fn_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    Fn G A g x = true ↔ ((∃ a ∈ A, x a = true) ∨
      ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ∨ g x = true := by
  simp only [Fn, Bool.or_eq_true, decide_eq_true_eq]

private lemma Fn_zero {n : ℕ} {W : Finset (Fin n)} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {g : (Fin n → Bool) → Bool} (hg : Ign W g) (ht : Touch W G) (hA : A ⊆ W)
    (z : Fin n → Bool) (hz : g z = false) : Fn G A g (zeroW W z) = false := by
  rw [← Bool.not_eq_true, Fn_true_iff]
  rintro ((⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩) | h)
  · simp [zeroW, hA ha] at hxa
  · rcases ht i j hij with h | h
    · simp [zeroW, h] at hi
    · simp [zeroW, h] at hj
  · have h2 : g (zeroW W z) = g z := hg _ _ (fun i hi => by simp [zeroW, hi])
    rw [h2, hz] at h
    exact Bool.false_ne_true h

private lemma Fn_indep {n : ℕ} {W : Finset (Fin n)} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {g : (Fin n → Bool) → Bool} (hg : Ign W g) (v : Fin n) (hvW : v ∈ W) (hvA : v ∉ A)
    (hv : ∀ w, ¬ G.Adj v w) (x : Fin n → Bool) (b : Bool) :
    Fn G A g (Function.update x v b) = Fn G A g x := by
  apply Bool.eq_iff_iff.mpr
  rw [Fn_true_iff, Fn_true_iff]
  have hup : ∀ i, i ≠ v → Function.update x v b i = x i := fun i hi => Function.update_of_ne hi _ _
  have hgx : g (Function.update x v b) = g x := hg _ _ (fun i hi => hup i (by
    rintro rfl
    exact hi hvW))
  constructor
  · rintro ((⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩) | h)
    · have hav : a ≠ v := by
        rintro rfl
        exact hvA ha
      rw [hup a hav] at hxa
      exact Or.inl (Or.inl ⟨a, ha, hxa⟩)
    · have hiv : i ≠ v := by
        rintro rfl
        exact hv j hij
      have hjv : j ≠ v := by
        rintro rfl
        exact hv i hij.symm
      rw [hup i hiv] at hi
      rw [hup j hjv] at hj
      exact Or.inl (Or.inr ⟨i, j, hij, hi, hj⟩)
    · rw [hgx] at h
      exact Or.inr h
  · rintro ((⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩) | h)
    · have hav : a ≠ v := by
        rintro rfl
        exact hvA ha
      exact Or.inl (Or.inl ⟨a, ha, by rw [hup a hav]; exact hxa⟩)
    · have hiv : i ≠ v := by
        rintro rfl
        exact hv j hij
      have hjv : j ≠ v := by
        rintro rfl
        exact hv i hij.symm
      exact Or.inl (Or.inr ⟨i, j, hij, by rw [hup i hiv]; exact hi, by rw [hup j hjv]; exact hj⟩)
    · exact Or.inr (by rw [hgx]; exact h)

private lemma Fn_varies {n : ℕ} {W : Finset (Fin n)} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    {g : (Fin n → Bool) → Bool} (hg : Ign W g) (ht : Touch W G) (hA : A ⊆ W)
    (y z : Fin n → Bool) (hy : g y = true) (hz : g z = false) :
    ∃ x x' : Fin n → Bool, Fn G A g x ≠ Fn G A g x' := by
  refine ⟨y, zeroW W z, ?_⟩
  rw [Fn_zero hg ht hA z hz, (Fn_true_iff G A g y).mpr (Or.inr hy)]
  decide

private lemma Fn_del {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (p l : Fin n) (hpl : G.Adj p l) (x : Fin n → Bool) :
    Fn G A g x = (Fn (G.deleteEdges {s(p, l)}) A g x || (x p && x l)) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.or_eq_true, Bool.and_eq_true, Fn_true_iff, Fn_true_iff]
  constructor
  · rintro ((hA | ⟨i, j, hij, hi, hj⟩) | hgx)
    · exact Or.inl (Or.inl (Or.inl hA))
    · by_cases he : s(i, j) = s(p, l)
      · rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1] at hi
          rw [h2] at hj
          exact Or.inr ⟨hi, hj⟩
        · rw [h1] at hi
          rw [h2] at hj
          exact Or.inr ⟨hj, hi⟩
      · refine Or.inl (Or.inl (Or.inr ⟨i, j, ?_, hi, hj⟩))
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hij, he⟩
    · exact Or.inl (Or.inr hgx)
  · rintro (((hA | ⟨i, j, hij, hi, hj⟩) | hgx) | ⟨hp, hl⟩)
    · exact Or.inl (Or.inl hA)
    · rw [SimpleGraph.deleteEdges_adj] at hij
      exact Or.inl (Or.inr ⟨i, j, hij.1, hi, hj⟩)
    · exact Or.inr hgx
    · exact Or.inl (Or.inr ⟨p, l, hpl, hp, hl⟩)

private lemma ncard_del {n : ℕ} (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    G.edgeSet.ncard ≤ (G.deleteEdges {e}).edgeSet.ncard + 1 := by
  have hsub : G.edgeSet ⊆ insert e (G.deleteEdges {e}).edgeSet := by
    intro x hx
    by_cases h : x = e
    · exact Or.inl h
    · right
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨hx, h⟩
  exact le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_insert_le _ _)

private lemma edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (c : ℕ)
    (hS : S.ncard ≤ c) (h : ∀ i j, G.Adj i j → s(i, j) ∈ S) : G.edgeSet.ncard ≤ c := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite S)) hS
  intro e he
  induction e using Sym2.ind with
  | _ i j => exact h i j he

private lemma lift {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (g : (Fin n → Bool) → Bool)
    (G G' : SimpleGraph (Fin n)) (c : Fin n) (k s1 s : ℕ)
    (hc0 : c ≠ pv 0) (hc1 : c ≠ pv (m + 1))
    (hD : ∀ i j, G.Adj i j → G'.Adj i j ∨ i = c ∨ j = c)
    (hE : G.edgeSet.ncard ≤ G'.edgeSet.ncard + k)
    (hs : s1 + k + 1 ≤ s)
    (h : Concl m pv G' ∅ g s1) : Concl m pv G ∅ g s := by
  obtain ⟨bu, bv, T, s', hcov, hu, hv, hsz, hineq⟩ := h
  refine ⟨bu, bv, insert c T, s', ?_, ?_, ?_, hsz, ?_⟩
  · intro i j hij
    rcases hD i j hij with h | h | h
    · rcases hcov i j h with h' | h'
      · exact Or.inl (Finset.mem_insert_of_mem h')
      · exact Or.inr (Finset.mem_insert_of_mem h')
    · left
      rw [h]
      exact Finset.mem_insert_self c T
    · right
      rw [h]
      exact Finset.mem_insert_self c T
  · rw [Finset.mem_insert]
    exact ⟨fun h => h.elim (fun h => absurd h.symm hc0) hu.mp, fun h => Or.inr (hu.mpr h)⟩
  · rw [Finset.mem_insert]
    exact ⟨fun h => h.elim (fun h => absurd h.symm hc1) hv.mp, fun h => Or.inr (hv.mpr h)⟩
  · have hcard := Finset.card_insert_le c T
    omega

private lemma step_b {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (W : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (hg : Ign W g) (y : Fin n → Bool) (hy : g y = true)
    (G : SimpleGraph (Fin n)) (l p t : Fin n) (s : ℕ)
    (ht : Touch W G) (hlW : l ∈ W) (hpW : p ∈ W)
    (hl0 : l ≠ pv 0) (hl1 : l ≠ pv (m + 1)) (hp0 : p ≠ pv 0) (hp1 : p ≠ pv (m + 1))
    (hlt : l ≠ t) (hpl : G.Adj p l) (hpt : G.Adj p t)
    (hl : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = t)
    (z : Fin n → Bool) (hz : g z = false) (hzt : t ∈ W ∨ z t = false)
    (hs : HasCircuitSize n (Fn G ∅ g) s)
    (IH : ∀ G' : SimpleGraph (Fin n), G' ≤ G → ¬ G'.Adj p l → ∀ s1 : ℕ,
      HasCircuitSize n (Fn G' ∅ g) s1 → Concl m pv G' ∅ g s1) :
    Concl m pv G ∅ g s := by
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = G.deleteEdges {s(p, l)} := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = G1.deleteEdges {s(p, t)} := ⟨_, rfl⟩
  have hG1le : G1 ≤ G := by
    rw [hG1]
    exact SimpleGraph.deleteEdges_le _
  have hG2le1 : G2 ≤ G1 := by
    rw [hG2]
    exact SimpleGraph.deleteEdges_le _
  have hG2le : G2 ≤ G := le_trans hG2le1 hG1le
  have hne_pl : p ≠ l := hpl.ne
  have hne_pt : p ≠ t := hpt.ne
  have hG1pt : G1.Adj p t := by
    rw [hG1, SimpleGraph.deleteEdges_adj]
    refine ⟨hpt, ?_⟩
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hlt h2.symm
    · exact hne_pl h1
  have hG1npl : ¬ G1.Adj p l := by
    rw [hG1, SimpleGraph.deleteEdges_adj]
    exact fun h => h.2 rfl
  have hG2npl : ¬ G2.Adj p l := fun h => hG1npl (hG2le1 h)
  have hG2l : ∀ w, ¬ G2.Adj l w := by
    intro w h
    have hw := hl w (hG2le h)
    rw [hw] at h
    exact hG2npl h.symm
  have hG2p : ∀ w, ¬ G2.Adj p w := by
    intro w h
    rcases hp w (hG2le h) with hw | hw
    · rw [hw] at h
      exact hG2npl h
    · rw [hw, hG2, SimpleGraph.deleteEdges_adj] at h
      exact h.2 rfl
  have ht2 : Touch W G2 := fun i j h => ht i j (hG2le h)
  have hfun1 : ∀ x, Fn G1 ∅ g x = (Fn G2 ∅ g x || (x p && x t)) := by
    intro x
    rw [hG2]
    exact Fn_del G1 ∅ g p t hG1pt x
  have hfun : Fn G ∅ g = fun x => Fn G2 ∅ g x || (x p && (x t || x l)) := by
    funext x
    rw [Fn_del G ∅ g p l hpl x, ← hG1, hfun1 x, Bool.and_or_distrib_left, Bool.or_assoc]
  rw [hfun] at hs
  have hindl : ∀ x b, Fn G2 ∅ g (Function.update x l b) = Fn G2 ∅ g x :=
    fun x b => Fn_indep hg l hlW (by simp) hG2l x b
  have hindp : ∀ x b, Fn G2 ∅ g (Function.update x p b) = Fn G2 ∅ g x :=
    fun x b => Fn_indep hg p hpW (by simp) hG2p x b
  have hvar := Fn_varies (A := ∅) hg ht2 (Finset.empty_subset W) y z hy hz
  have hposs : ∃ x, Fn G2 ∅ g x = false ∧ x t = false := by
    refine ⟨zeroW W z, Fn_zero hg ht2 (Finset.empty_subset W) z hz, ?_⟩
    by_cases htW : t ∈ W
    · simp [zeroW, htW]
    · rcases hzt with h | h
      · exact absurd h htW
      · simp [zeroW, htW, h]
  rcases Path574.peel_two (Fn G2 ∅ g) l p t hne_pl.symm hlt hne_pt hindl hindp hvar hposs hs with
    ⟨a1, ha1, hsz1⟩ | ⟨a2, ha2, hsz2⟩
  · have hsz1' : HasCircuitSize n (Fn G1 ∅ g) a1 := by
      have hf : Fn G1 ∅ g = fun x => Fn G2 ∅ g x || (x p && x t) := funext hfun1
      rw [hf]
      exact hsz1
    have hc := IH G1 hG1le hG1npl a1 hsz1'
    refine lift m pv g G G1 l 1 a1 s hl0 hl1 ?_ ?_ (by omega) hc
    · intro i j hij
      by_cases he : s(i, j) = s(p, l)
      · rcases Sym2.eq_iff.mp he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr h2)
        · exact Or.inr (Or.inl h1)
      · left
        rw [hG1, SimpleGraph.deleteEdges_adj]
        exact ⟨hij, he⟩
    · rw [hG1]
      exact ncard_del G _
  · have hc := IH G2 hG2le hG2npl a2 hsz2
    refine lift m pv g G G2 p 2 a2 s hp0 hp1 ?_ ?_ (by omega) hc
    · intro i j hij
      by_cases he : s(i, j) = s(p, l)
      · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
      · by_cases he2 : s(i, j) = s(p, t)
        · rcases Sym2.eq_iff.mp he2 with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h2)
        · left
          rw [hG2, SimpleGraph.deleteEdges_adj, hG1, SimpleGraph.deleteEdges_adj]
          exact ⟨⟨hij, he⟩, he2⟩
    · have h1 : G.edgeSet.ncard ≤ G1.edgeSet.ncard + 1 := by
        rw [hG1]
        exact ncard_del G _
      have h2 : G1.edgeSet.ncard ≤ G2.edgeSet.ncard + 1 := by
        rw [hG2]
        exact ncard_del G1 _
      omega

private lemma step_a {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (W : Finset (Fin n))
    (g : (Fin n → Bool) → Bool) (hg : Ign W g) (y : Fin n → Bool) (hy : g y = true)
    (G : SimpleGraph (Fin n)) (l p : Fin n) (s : ℕ)
    (ht : Touch W G) (hlW : l ∈ W) (hpW : p ∈ W)
    (hp0 : p ≠ pv 0) (hp1 : p ≠ pv (m + 1)) (hpl : G.Adj p l)
    (hl : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l)
    (z : Fin n → Bool) (hz : g z = false)
    (hs : HasCircuitSize n (Fn G ∅ g) s)
    (IH : ∀ G' : SimpleGraph (Fin n), G' ≤ G → ¬ G'.Adj p l → ∀ s1 : ℕ,
      HasCircuitSize n (Fn G' ∅ g) s1 → Concl m pv G' ∅ g s1) :
    Concl m pv G ∅ g s := by
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = G.deleteEdges {s(p, l)} := ⟨_, rfl⟩
  have hG1le : G1 ≤ G := by
    rw [hG1]
    exact SimpleGraph.deleteEdges_le _
  have hne : p ≠ l := hpl.ne
  have hG1npl : ¬ G1.Adj p l := by
    rw [hG1, SimpleGraph.deleteEdges_adj]
    exact fun h => h.2 rfl
  have hG1l : ∀ w, ¬ G1.Adj l w := by
    intro w h
    have hw := hl w (hG1le h)
    rw [hw] at h
    exact hG1npl h.symm
  have hG1p : ∀ w, ¬ G1.Adj p w := by
    intro w h
    have hw := hp w (hG1le h)
    rw [hw] at h
    exact hG1npl h
  have ht1 : Touch W G1 := fun i j h => ht i j (hG1le h)
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → Bool) → Bool, F = fun x => Fn G1 ∅ g x || (x p && x l) :=
    ⟨_, rfl⟩
  have hfun : Fn G ∅ g = F := by
    rw [hF]
    funext x
    rw [Fn_del G ∅ g p l hpl x, ← hG1]
  rw [hfun] at hs
  have hindl : ∀ x b, Fn G1 ∅ g (Function.update x l b) = Fn G1 ∅ g x :=
    fun x b => Fn_indep hg l hlW (by simp) hG1l x b
  have hindp : ∀ x b, Fn G1 ∅ g (Function.update x p b) = Fn G1 ∅ g x :=
    fun x b => Fn_indep hg p hpW (by simp) hG1p x b
  obtain ⟨x0, x1, hvar⟩ := Fn_varies (A := ∅) hg ht1 (Finset.empty_subset W) y z hy hz
  have hzero := Fn_zero hg ht1 (Finset.empty_subset W) z hz
  have hoff : ∀ x, F (Function.update x l false) = Fn G1 ∅ g x := by
    intro x
    rw [hF]
    show (Fn G1 ∅ g (Function.update x l false) ||
      (Function.update x l false p && Function.update x l false l)) = Fn G1 ∅ g x
    rw [hindl, Function.update_self, Bool.and_false, Bool.or_false]
  have hon : ∀ x, F (Function.update x l true) = (Fn G1 ∅ g x || x p) := by
    intro x
    rw [hF]
    show (Fn G1 ∅ g (Function.update x l true) ||
      (Function.update x l true p && Function.update x l true l)) = (Fn G1 ∅ g x || x p)
    rw [hindl, Function.update_self, Bool.and_true, Function.update_of_ne hne]
  have hzp : zeroW W z p = false := by simp [zeroW, hpW]
  obtain ⟨h2, hcase⟩ := PathGateReduction.elim_two_var (F := F) l hs
    ⟨Function.update (zeroW W z) p true, by
      rw [hoff, hon, hindp, hzero, Function.update_self]
      decide⟩
    ⟨x0, x1, by
      rw [hoff, hoff]
      exact hvar⟩
    ⟨zeroW W z, y, by
      rw [hon, hon, hzero, (Fn_true_iff G1 ∅ g y).mpr (Or.inr hy), hzp]
      simp⟩
  have hB : ∃ a1, a1 + 2 ≤ s ∧ HasCircuitSize n (Fn G1 ∅ g) a1 := by
    rcases hcase with h | h
    · refine ⟨s - 2, by omega, ?_⟩
      have hf : (fun x => F (Function.update x l false)) = Fn G1 ∅ g := funext hoff
      rw [hf] at h
      exact h
    · have hf : (fun x => F (Function.update x l true)) = fun x => Fn G1 ∅ g x || x p :=
        funext hon
      rw [hf] at h
      obtain ⟨h3, h4⟩ := Path574.remove_bare (Fn G1 ∅ g) p hindp ⟨x0, x1, hvar⟩ h
      exact ⟨s - 2 - 1, by omega, h4⟩
  obtain ⟨a1, ha1, hsz1⟩ := hB
  have hc := IH G1 hG1le hG1npl a1 hsz1
  refine lift m pv g G G1 p 1 a1 s hp0 hp1 ?_ ?_ (by omega) hc
  · intro i j hij
    by_cases he : s(i, j) = s(p, l)
    · rcases Sym2.eq_iff.mp he with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h2)
    · left
      rw [hG1, SimpleGraph.deleteEdges_adj]
      exact ⟨hij, he⟩
  · rw [hG1]
    exact ncard_del G _

private lemma adj_cases {n : ℕ} {m : ℕ} {pv : ℕ → Fin n} {G : SimpleGraph (Fin n)}
    (hinj : ∀ k l : ℕ, k ≤ m + 1 → l ≤ m + 1 → pv k = pv l → k = l) (hsub : Sub m pv G)
    (k : ℕ) (hk : k ≤ m + 1) (w : Fin n) (h : G.Adj (pv k) w) :
    (k ≤ m ∧ w = pv (k + 1)) ∨ (1 ≤ k ∧ w = pv (k - 1)) := by
  obtain ⟨j, hj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hsub _ _ h
  · have hjk := hinj j k (by omega) hk h1
    subst hjk
    exact Or.inl ⟨hj, h2.symm⟩
  · have hjk := hinj (j + 1) k (by omega) hk h2
    subst hjk
    exact Or.inr ⟨by omega, by rw [Nat.add_sub_cancel]; exact h1.symm⟩

private lemma base_aux {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (g : (Fin n → Bool) → Bool)
    (G : SimpleGraph (Fin n)) (s : ℕ) (bu bv : Bool) (T : Finset (Fin n))
    (hedge : ∀ i j, G.Adj i j →
      (bu = true ∧ ((i = pv 0 ∧ j = pv 1) ∨ (i = pv 1 ∧ j = pv 0))) ∨
      (bv = true ∧ ((i = pv m ∧ j = pv (m + 1)) ∨ (i = pv (m + 1) ∧ j = pv m))))
    (hbu : bu = true → G.Adj (pv 0) (pv 1)) (hbv : bv = true → G.Adj (pv m) (pv (m + 1)))
    (hu : pv 0 ∈ T ↔ bu = true) (hv : pv (m + 1) ∈ T ↔ bv = true)
    (hcount : G.edgeSet.ncard + T.card +
      ((if bu = true then 0 else 2) + (if bv = true then 0 else 2)) ≤ 4)
    (hs : HasCircuitSize n (Fn G ∅ g) s) : Concl m pv G ∅ g s := by
  refine ⟨bu, bv, T, s, ?_, hu, hv, ?_, ?_⟩
  · intro i j hij
    rcases hedge i j hij with ⟨hb, ⟨h1, _⟩ | ⟨_, h2⟩⟩ | ⟨hb, ⟨_, h2⟩ | ⟨h1, _⟩⟩
    · left
      rw [h1]
      exact hu.mpr hb
    · right
      rw [h2]
      exact hu.mpr hb
    · right
      rw [h2]
      exact hv.mpr hb
    · left
      rw [h1]
      exact hv.mpr hb
  · have hfun : (fun x : Fin n → Bool => g x || (bu && x (pv 0) && x (pv 1)) ||
        (bv && x (pv m) && x (pv (m + 1)))) = Fn G ∅ g := by
      funext x
      apply Bool.eq_iff_iff.mpr
      rw [Fn_true_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true]
      constructor
      · rintro ((hgx | ⟨⟨hb, h0⟩, h1⟩) | ⟨⟨hb, h0⟩, h1⟩)
        · exact Or.inr hgx
        · exact Or.inl (Or.inr ⟨pv 0, pv 1, hbu hb, h0, h1⟩)
        · exact Or.inl (Or.inr ⟨pv m, pv (m + 1), hbv hb, h0, h1⟩)
      · rintro ((⟨a, ha, _⟩ | ⟨i, j, hij, hi, hj⟩) | hgx)
        · simp at ha
        · rcases hedge i j hij with ⟨hb, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨hb, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · rw [h1] at hi
            rw [h2] at hj
            exact Or.inl (Or.inr ⟨⟨hb, hi⟩, hj⟩)
          · rw [h1] at hi
            rw [h2] at hj
            exact Or.inl (Or.inr ⟨⟨hb, hj⟩, hi⟩)
          · rw [h1] at hi
            rw [h2] at hj
            exact Or.inr ⟨⟨hb, hi⟩, hj⟩
          · rw [h1] at hi
            rw [h2] at hj
            exact Or.inr ⟨⟨hb, hj⟩, hi⟩
        · exact Or.inl (Or.inl hgx)
    rw [hfun]
    exact hs
  · rw [Finset.card_empty]
    omega

private lemma base {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (g : (Fin n → Bool) → Bool)
    (hinj : ∀ k l : ℕ, k ≤ m + 1 → l ≤ m + 1 → pv k = pv l → k = l)
    (G : SimpleGraph (Fin n)) (hsub : Sub m pv G) (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m)
    (ha : a ≤ 1) (hb : m ≤ b + 1) (hwin : Win pv G a b) (s : ℕ)
    (hs : HasCircuitSize n (Fn G ∅ g) s) : Concl m pv G ∅ g s := by
  have hedge : ∀ i j, G.Adj i j →
      (G.Adj (pv 0) (pv 1) ∧ ((i = pv 0 ∧ j = pv 1) ∨ (i = pv 1 ∧ j = pv 0))) ∨
      (G.Adj (pv m) (pv (m + 1)) ∧ ((i = pv m ∧ j = pv (m + 1)) ∨ (i = pv (m + 1) ∧ j = pv m))) := by
    intro i j hij
    obtain ⟨k, hk, h⟩ := hsub i j hij
    have hadj : G.Adj (pv k) (pv (k + 1)) := by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
        exact hij
      · rw [h1, h2]
        exact hij.symm
    have hk' : k = 0 ∨ k = m := by
      by_contra hne
      have h1 : k ≠ 0 := fun h => hne (Or.inl h)
      have h2 : k ≠ m := fun h => hne (Or.inr h)
      exact hwin k (by omega) (by omega) hadj
    rcases hk' with hk0 | hkm
    · left
      rw [hk0] at hadj h
      refine ⟨hadj, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    · right
      rw [hkm] at hadj h
      refine ⟨hadj, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
  have hne : pv 0 ≠ pv (m + 1) := fun h => by
    have := hinj 0 (m + 1) (by omega) le_rfl h
    omega
  by_cases h0 : G.Adj (pv 0) (pv 1)
  · by_cases hm : G.Adj (pv m) (pv (m + 1))
    · refine base_aux m pv g G s true true {pv 0, pv (m + 1)} ?_ (fun _ => h0) (fun _ => hm)
        ?_ ?_ ?_ hs
      · intro i j hij
        rcases hedge i j hij with ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨rfl, h⟩
      · simp
      · simp
      · have hE : G.edgeSet.ncard ≤ 2 := by
          refine edge_bound G {s(pv 0, pv 1), s(pv m, pv (m + 1))} 2 ?_ ?_
          · exact le_trans (Set.ncard_insert_le _ _) (by rw [Set.ncard_singleton])
          · intro i j hij
            rcases hedge i j hij with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl (Sym2.eq_iff.mpr h)
            · exact Or.inr (Sym2.eq_iff.mpr h)
        have hT : ({pv 0, pv (m + 1)} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
        show G.edgeSet.ncard + ({pv 0, pv (m + 1)} : Finset (Fin n)).card + (0 + 0) ≤ 4
        omega
    · refine base_aux m pv g G s true false {pv 0} ?_ (fun _ => h0) (fun h => by simp at h)
        ?_ ?_ ?_ hs
      · intro i j hij
        rcases hedge i j hij with ⟨_, h⟩ | ⟨h', _⟩
        · exact Or.inl ⟨rfl, h⟩
        · exact absurd h' hm
      · simp
      · simp [hne.symm]
      · have hE : G.edgeSet.ncard ≤ 1 := by
          refine edge_bound G {s(pv 0, pv 1)} 1 ?_ ?_
          · rw [Set.ncard_singleton]
          · intro i j hij
            rcases hedge i j hij with ⟨_, h⟩ | ⟨h', _⟩
            · exact Sym2.eq_iff.mpr h
            · exact absurd h' hm
        show G.edgeSet.ncard + ({pv 0} : Finset (Fin n)).card + (0 + 2) ≤ 4
        rw [Finset.card_singleton]
        omega
  · by_cases hm : G.Adj (pv m) (pv (m + 1))
    · refine base_aux m pv g G s false true {pv (m + 1)} ?_ (fun h => by simp at h) (fun _ => hm)
        ?_ ?_ ?_ hs
      · intro i j hij
        rcases hedge i j hij with ⟨h', _⟩ | ⟨_, h⟩
        · exact absurd h' h0
        · exact Or.inr ⟨rfl, h⟩
      · simp [hne]
      · simp
      · have hE : G.edgeSet.ncard ≤ 1 := by
          refine edge_bound G {s(pv m, pv (m + 1))} 1 ?_ ?_
          · rw [Set.ncard_singleton]
          · intro i j hij
            rcases hedge i j hij with ⟨h', _⟩ | ⟨_, h⟩
            · exact absurd h' h0
            · exact Sym2.eq_iff.mpr h
        show G.edgeSet.ncard + ({pv (m + 1)} : Finset (Fin n)).card + (2 + 0) ≤ 4
        rw [Finset.card_singleton]
        omega
    · refine base_aux m pv g G s false false ∅ ?_ (fun h => by simp at h) (fun h => by simp at h)
        ?_ ?_ ?_ hs
      · intro i j hij
        rcases hedge i j hij with ⟨h', _⟩ | ⟨h', _⟩
        · exact absurd h' h0
        · exact absurd h' hm
      · simp
      · simp
      · have hE : G.edgeSet.ncard ≤ 0 := by
          refine edge_bound G ∅ 0 ?_ ?_
          · rw [Set.ncard_empty]
          · intro i j hij
            rcases hedge i j hij with ⟨h', _⟩ | ⟨h', _⟩
            · exact absurd h' h0
            · exact absurd h' hm
        show G.edgeSet.ncard + (∅ : Finset (Fin n)).card + (2 + 2) ≤ 4
        rw [Finset.card_empty]
        omega

private lemma peel_all {n : ℕ} (m : ℕ) (pv : ℕ → Fin n) (W : Finset (Fin n))
    (g : (Fin n → Bool) → Bool)
    (hinj : ∀ k l : ℕ, k ≤ m + 1 → l ≤ m + 1 → pv k = pv l → k = l)
    (hW : ∀ i : Fin n, i ∈ W ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ pv k = i)
    (hg : Ign W g) (y : Fin n → Bool) (hy : g y = true)
    (zu : Fin n → Bool) (hzu : g zu = false) (hzu0 : zu (pv 0) = false)
    (zv : Fin n → Bool) (hzv : g zv = false) (hzv1 : zv (pv (m + 1)) = false) :
    ∀ (d a b : ℕ), a + (m - b) ≤ d → a ≤ b → b ≤ m → ∀ G : SimpleGraph (Fin n),
      Sub m pv G → Touch W G → Win pv G a b →
      ∀ s : ℕ, HasCircuitSize n (Fn G ∅ g) s → Concl m pv G ∅ g s := by
  have memW : ∀ k, 1 ≤ k → k ≤ m → pv k ∈ W := fun k h1 h2 => (hW _).mpr ⟨k, h1, h2, rfl⟩
  have ne0 : ∀ k, 1 ≤ k → k ≤ m + 1 → pv k ≠ pv 0 := fun k h1 h2 h => by
    have := hinj k 0 h2 (by omega) h
    omega
  have ne1 : ∀ k, k ≤ m → pv k ≠ pv (m + 1) := fun k h1 h => by
    have := hinj k (m + 1) (by omega) le_rfl h
    omega
  intro d
  induction d with
  | zero =>
    intro a b hd hab hbm G hsub ht hwin s hs
    exact base m pv g hinj G hsub a b hab hbm (by omega) (by omega) hwin s hs
  | succ d ih =>
    intro a b hd hab hbm G hsub ht hwin s hs
    by_cases ha : a ≤ 1
    · by_cases hb : m ≤ b + 1
      · exact base m pv g hinj G hsub a b hab hbm ha hb hwin s hs
      · obtain ⟨c, hc⟩ : ∃ c, c = b + 1 := ⟨_, rfl⟩
        by_cases he : G.Adj (pv c) (pv (c + 1))
        · have hlW : pv c ∈ W := memW c (by omega) (by omega)
          have hpW : pv (c + 1) ∈ W := memW (c + 1) (by omega) (by omega)
          have hIH : ∀ G' : SimpleGraph (Fin n), G' ≤ G → ¬ G'.Adj (pv (c + 1)) (pv c) →
              ∀ s1 : ℕ, HasCircuitSize n (Fn G' ∅ g) s1 → Concl m pv G' ∅ g s1 := by
            intro G' hle hno s1 hs1
            refine ih a c (by omega) (by omega) (by omega) G' (fun i j h => hsub i j (hle h))
              (fun i j h => ht i j (hle h)) ?_ s1 hs1
            intro k hk1 hk2 hadj
            by_cases hkc : k = c
            · rw [hkc] at hadj
              exact hno hadj.symm
            · exact hwin k hk1 (by omega) (hle hadj)
          have hl : ∀ w, G.Adj (pv c) w → w = pv (c + 1) := by
            intro w hw
            rcases adj_cases hinj hsub c (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact h2
            · exfalso
              have hcb : c - 1 = b := by omega
              rw [h2, hcb] at hw
              have hw' : G.Adj (pv b) (pv (b + 1)) := by
                rw [← hc]
                exact hw.symm
              exact hwin b hab le_rfl hw'
          by_cases he2 : G.Adj (pv (c + 1)) (pv (c + 1 + 1))
          · have hp : ∀ w, G.Adj (pv (c + 1)) w → w = pv c ∨ w = pv (c + 1 + 1) := by
              intro w hw
              rcases adj_cases hinj hsub (c + 1) (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact Or.inr h2
              · left
                rw [h2, Nat.add_sub_cancel]
            have hzt : ∃ z : Fin n → Bool, g z = false ∧
                (pv (c + 1 + 1) ∈ W ∨ z (pv (c + 1 + 1)) = false) := by
              by_cases hend : c + 1 + 1 = m + 1
              · refine ⟨zv, hzv, Or.inr ?_⟩
                rw [hend]
                exact hzv1
              · exact ⟨zu, hzu, Or.inl (memW (c + 1 + 1) (by omega) (by omega))⟩
            obtain ⟨z, hz, hzt'⟩ := hzt
            have hlt : pv c ≠ pv (c + 1 + 1) := fun h => by
              have := hinj c (c + 1 + 1) (by omega) (by omega) h
              omega
            exact step_b m pv W g hg y hy G (pv c) (pv (c + 1)) (pv (c + 1 + 1)) s ht hlW hpW
              (ne0 c (by omega) (by omega)) (ne1 c (by omega))
              (ne0 (c + 1) (by omega) (by omega)) (ne1 (c + 1) (by omega))
              hlt he.symm he2 hl hp z hz hzt' hs hIH
          · have hp : ∀ w, G.Adj (pv (c + 1)) w → w = pv c := by
              intro w hw
              rcases adj_cases hinj hsub (c + 1) (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
              · exfalso
                rw [h2] at hw
                exact he2 hw
              · rw [h2, Nat.add_sub_cancel]
            exact step_a m pv W g hg y hy G (pv c) (pv (c + 1)) s ht hlW hpW
              (ne0 (c + 1) (by omega) (by omega)) (ne1 (c + 1) (by omega))
              he.symm hl hp zu hzu hs hIH
        · refine ih a c (by omega) (by omega) (by omega) G hsub ht ?_ s hs
          intro k hk1 hk2 hadj
          by_cases hkc : k = c
          · rw [hkc] at hadj
            exact he hadj
          · exact hwin k hk1 (by omega) hadj
    · obtain ⟨c, hc⟩ : ∃ c, a = c + 1 + 1 := ⟨a - 2, by omega⟩
      by_cases he : G.Adj (pv (c + 1)) (pv (c + 1 + 1))
      · have hlW : pv (c + 1 + 1) ∈ W := memW (c + 1 + 1) (by omega) (by omega)
        have hpW : pv (c + 1) ∈ W := memW (c + 1) (by omega) (by omega)
        have hIH : ∀ G' : SimpleGraph (Fin n), G' ≤ G → ¬ G'.Adj (pv (c + 1)) (pv (c + 1 + 1)) →
            ∀ s1 : ℕ, HasCircuitSize n (Fn G' ∅ g) s1 → Concl m pv G' ∅ g s1 := by
          intro G' hle hno s1 hs1
          refine ih (c + 1) b (by omega) (by omega) hbm G' (fun i j h => hsub i j (hle h))
            (fun i j h => ht i j (hle h)) ?_ s1 hs1
          intro k hk1 hk2 hadj
          by_cases hkc : k = c + 1
          · rw [hkc] at hadj
            exact hno hadj
          · exact hwin k (by omega) hk2 (hle hadj)
        have hl : ∀ w, G.Adj (pv (c + 1 + 1)) w → w = pv (c + 1) := by
          intro w hw
          rcases adj_cases hinj hsub (c + 1 + 1) (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
          · exfalso
            rw [h2] at hw
            exact hwin (c + 1 + 1) (by omega) (by omega) hw
          · rw [h2, Nat.add_sub_cancel]
        by_cases he2 : G.Adj (pv c) (pv (c + 1))
        · have hp : ∀ w, G.Adj (pv (c + 1)) w → w = pv (c + 1 + 1) ∨ w = pv c := by
            intro w hw
            rcases adj_cases hinj hsub (c + 1) (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact Or.inl h2
            · right
              rw [h2, Nat.add_sub_cancel]
          have hzt : pv c ∈ W ∨ zu (pv c) = false := by
            by_cases hc0 : c = 0
            · right
              rw [hc0]
              exact hzu0
            · exact Or.inl (memW c (by omega) (by omega))
          have hlt : pv (c + 1 + 1) ≠ pv c := fun h => by
            have := hinj (c + 1 + 1) c (by omega) (by omega) h
            omega
          exact step_b m pv W g hg y hy G (pv (c + 1 + 1)) (pv (c + 1)) (pv c) s ht hlW hpW
            (ne0 (c + 1 + 1) (by omega) (by omega)) (ne1 (c + 1 + 1) (by omega))
            (ne0 (c + 1) (by omega) (by omega)) (ne1 (c + 1) (by omega))
            hlt he he2.symm hl hp zu hzu hzt hs hIH
        · have hp : ∀ w, G.Adj (pv (c + 1)) w → w = pv (c + 1 + 1) := by
            intro w hw
            rcases adj_cases hinj hsub (c + 1) (by omega) w hw with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact h2
            · exfalso
              rw [h2, Nat.add_sub_cancel] at hw
              exact he2 hw.symm
          exact step_a m pv W g hg y hy G (pv (c + 1 + 1)) (pv (c + 1)) s ht hlW hpW
            (ne0 (c + 1) (by omega) (by omega)) (ne1 (c + 1) (by omega))
            he hl hp zu hzu hs hIH
      · refine ih (c + 1) b (by omega) (by omega) hbm G hsub ht ?_ s hs
        intro k hk1 hk2 hadj
        by_cases hkc : k = c + 1
        · rw [hkc] at hadj
          exact he hadj
        · exact hwin k (by omega) hk2 hadj

end Peel580

theorem PEqualNP.Outside.L_meta_580 : ∀ (n m : ℕ) (pv : ℕ → Fin n) (W A : Finset (Fin n)) (G : SimpleGraph (Fin n)) (g : (Fin n → Bool) → Bool) (s : ℕ), (∀ k l : ℕ, k ≤ m + 1 → l ≤ m + 1 → pv k = pv l → k = l) → (∀ i : Fin n, i ∈ W ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ pv k = i) → (∀ i j : Fin n, G.Adj i j → ∃ k : ℕ, k ≤ m ∧ ((pv k = i ∧ pv (k + 1) = j) ∨ (pv k = j ∧ pv (k + 1) = i))) → (∃ k : ℕ, k ≤ m ∧ ¬ G.Adj (pv k) (pv (k + 1))) → A ⊆ W → (∀ a ∈ A, ∀ w : Fin n, ¬ G.Adj a w) → (∀ x y : Fin n → Bool, (∀ i : Fin n, i ∉ W → x i = y i) → g x = g y) → (∃ y : Fin n → Bool, g y = true) → (∃ z : Fin n → Bool, g z = false ∧ z (pv 0) = false) → (∃ z : Fin n → Bool, g z = false ∧ z (pv (m + 1)) = false) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _) || g x) s → ∃ (bu bv : Bool) (T : Finset (Fin n)) (s' : ℕ), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ (pv 0 ∈ T ↔ bu = true) ∧ (pv (m + 1) ∈ T ↔ bv = true) ∧ PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => g x || (bu && x (pv 0) && x (pv 1)) || (bv && x (pv m) && x (pv (m + 1)))) s' ∧ A.card + G.edgeSet.ncard + T.card + ((if bu = true then 0 else 2) + (if bv = true then 0 else 2)) + s' ≤ s + 4 := by
  intro n m pv W A G g s hinj hW hsub hgap hAW hAfree hg hy hzu hzv hs
  obtain ⟨k0, hk0, hgap⟩ := hgap
  obtain ⟨y, hy⟩ := hy
  obtain ⟨zu, hzu, hzu0⟩ := hzu
  obtain ⟨zv, hzv, hzv1⟩ := hzv
  have memW : ∀ k, 1 ≤ k → k ≤ m → pv k ∈ W := fun k h1 h2 => (hW _).mpr ⟨k, h1, h2, rfl⟩
  have ht : Peel580.Touch W G := by
    intro i j hij
    obtain ⟨k, hk, h⟩ := hsub i j hij
    by_cases hk1 : 1 ≤ k
    · rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
      · left
        rw [← h1]
        exact memW k hk1 hk
      · right
        rw [← h1]
        exact memW k hk1 hk
    · have hk0' : k = 0 := by omega
      rw [hk0'] at h
      by_cases hm : 1 ≤ m
      · rcases h with ⟨_, h2⟩ | ⟨_, h2⟩
        · right
          rw [← h2]
          exact memW 1 le_rfl hm
        · left
          rw [← h2]
          exact memW 1 le_rfl hm
      · exfalso
        have hk00 : k0 = 0 := by omega
        rw [hk00] at hgap
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · apply hgap
          rw [h1, h2]
          exact hij
        · apply hgap
          rw [h1, h2]
          exact hij.symm
  have key : ∀ A : Finset (Fin n), A ⊆ W → (∀ a ∈ A, ∀ w : Fin n, ¬ G.Adj a w) → ∀ s : ℕ,
      HasCircuitSize n (Peel580.Fn G A g) s → Peel580.Concl m pv G A g s := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro _ _ s hs
      refine Peel580.peel_all m pv W g hinj hW hg y hy zu hzu hzu0 zv hzv hzv1
        (k0 + (m - k0)) k0 k0 le_rfl le_rfl hk0 G hsub ht ?_ s hs
      intro k h1 h2
      have hkk : k = k0 := by omega
      rw [hkk]
      exact hgap
    | insert a A ha ih =>
      intro hAW hAfree s hs
      have haW : a ∈ W := hAW (Finset.mem_insert_self a A)
      have hAW' : A ⊆ W := fun b hb => hAW (Finset.mem_insert_of_mem hb)
      have hAfree' : ∀ b ∈ A, ∀ w : Fin n, ¬ G.Adj b w :=
        fun b hb => hAfree b (Finset.mem_insert_of_mem hb)
      have hfun : Peel580.Fn G (insert a A) g = fun x => Peel580.Fn G A g x || x a := by
        funext x
        apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true, Peel580.Fn_true_iff, Peel580.Fn_true_iff]
        constructor
        · rintro ((⟨b, hb, hx⟩ | hE) | hgx)
          · rcases Finset.mem_insert.mp hb with hba | hbA
            · rw [hba] at hx
              exact Or.inr hx
            · exact Or.inl (Or.inl (Or.inl ⟨b, hbA, hx⟩))
          · exact Or.inl (Or.inl (Or.inr hE))
          · exact Or.inl (Or.inr hgx)
        · rintro (((⟨b, hb, hx⟩ | hE) | hgx) | hxa)
          · exact Or.inl (Or.inl ⟨b, Finset.mem_insert_of_mem hb, hx⟩)
          · exact Or.inl (Or.inr hE)
          · exact Or.inr hgx
          · exact Or.inl (Or.inl ⟨a, Finset.mem_insert_self a A, hxa⟩)
      rw [hfun] at hs
      obtain ⟨h1, h2⟩ := Path574.remove_bare (Peel580.Fn G A g) a
        (fun x b => Peel580.Fn_indep hg a haW ha (hAfree a (Finset.mem_insert_self a A)) x b)
        (Peel580.Fn_varies hg ht hAW' y zu hy hzu) hs
      obtain ⟨bu, bv, T, s', hcov, hu, hv, hsz, hineq⟩ := ih hAW' hAfree' (s - 1) h2
      refine ⟨bu, bv, T, s', hcov, hu, hv, hsz, ?_⟩
      rw [Finset.card_insert_of_notMem ha]
      omega
  exact key A hAW hAfree s hs
