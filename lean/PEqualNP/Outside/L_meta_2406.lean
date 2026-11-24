import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2406

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev st (n : ℕ) (C : Circuit) (ra rb : ℕ) : Prop :=
  ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧
    ra ∈ (gateAt C rj).inputs

abbrev RR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (st n C)

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma rr_le (n : ℕ) (C : Circuit) (a b : ℕ) (h : RR n C a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt hs.1)

lemma rr_cases (n : ℕ) (C : Circuit) (m w : ℕ) (h : RR n C m w) :
    m = w ∨ ∃ c, RR n C m c ∧ st n C c w := by
  rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, hs⟩
  · exact Or.inl h1.symm
  · exact Or.inr ⟨c, hc, hs⟩

lemma rr_step (n : ℕ) (C : Circuit) (k c i : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hc : c ∈ (gateAt C k).inputs) (hlt : c < n + k)
    (h : RR n C i c) : RR n C i (n + k) := by
  have hs : st n C c (n + k) := ⟨hlt, k, rfl, hk, hop, hc⟩
  exact Relation.ReflTransGen.tail h hs

lemma rr_notor (n : ℕ) (C : Circuit) (m w : ℕ)
    (hw : ¬ ∃ k, w = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or)
    (h : RR n C m w) : m = w := by
  rcases rr_cases n C m w h with h1 | ⟨c, _, hs⟩
  · exact h1
  · exfalso
    obtain ⟨_, rj, h1, h2, h3, _⟩ := hs
    exact hw ⟨rj, h1, h2, h3⟩

noncomputable def LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) : Finset α := by
  classical
  exact (labelled.filter (fun m => RR n C m w)).biUnion lab

lemma mem_LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) (x : α) :
    x ∈ LL n C labelled lab w ↔ ∃ m ∈ labelled, RR n C m w ∧ x ∈ lab m := by
  classical
  unfold LL
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨m, ⟨h1, h2⟩, h3⟩
    exact ⟨m, h1, h2, h3⟩
  · rintro ⟨m, h1, h2, h3⟩
    exact ⟨m, ⟨h1, h2⟩, h3⟩

lemma ncard_LL (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (w : ℕ) :
    ({x3 : α | ∃ m3 ∈ labelled, RR n C m3 w ∧ x3 ∈ lab m3}).ncard =
      (LL n C labelled lab w).card := by
  have hE : {x3 : α | ∃ m3 ∈ labelled, RR n C m3 w ∧ x3 ∈ lab m3} =
      ((LL n C labelled lab w : Finset α) : Set α) := by
    ext x
    rw [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (mem_LL n C labelled lab w x).symm
  rw [hE, Set.ncard_coe_finset]

lemma LL_small_notor (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hlab : ∀ m ∈ labelled, (lab m).card ≤ 2) (w : ℕ)
    (hw : ¬ ∃ k, w = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or) :
    (LL n C labelled lab w).card ≤ 2 := by
  by_cases hwl : w ∈ labelled
  · refine le_trans (Finset.card_le_card ?_) (hlab w hwl)
    intro x hx
    obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab w x).1 hx
    have hmw := rr_notor n C m w hw hr
    rw [← hmw]
    exact hxm
  · have hE : LL n C labelled lab w = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab w x).1 hx
      have hmw := rr_notor n C m w hw hr
      rw [hmw] at hm
      exact hwl hm
    rw [hE, Finset.card_empty]
    exact Nat.zero_le _

lemma LL_or (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α)
    (hnl : ∀ m ∈ labelled, m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (k a b : ℕ) (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b]) (x : α)
    (hx : x ∈ LL n C labelled lab (n + k)) :
    x ∈ LL n C labelled lab a ∨ x ∈ LL n C labelled lab b := by
  obtain ⟨m, hm, hr, hxm⟩ := (mem_LL n C labelled lab (n + k) x).1 hx
  rcases rr_cases n C m (n + k) hr with h1 | ⟨c, hc, hs⟩
  · exfalso
    rcases hnl m hm with h2 | ⟨j, h2, _, h4⟩
    · omega
    · have hjk : j = k := by omega
      rw [hjk, hop] at h4
      cases h4
  · obtain ⟨_, rj, h1, _, _, h4⟩ := hs
    have hjk : rj = k := by omega
    rw [hjk, hin, List.mem_cons, List.mem_singleton] at h4
    rcases h4 with h5 | h5
    · rw [h5] at hc
      exact Or.inl ((mem_LL n C labelled lab a x).2 ⟨m, hm, hc, hxm⟩)
    · rw [h5] at hc
      exact Or.inr ((mem_LL n C labelled lab b x).2 ⟨m, hm, hc, hxm⟩)

def bigP (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) (k : ℕ) : Prop :=
  (gateAt C k).op = GateOp.or ∧ (∃ w ∈ Q, RR n C (n + k) w) ∧
    3 ≤ (LL n C labelled lab (n + k)).card

noncomputable def big (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (bigP n C labelled lab Q)

lemma mem_big (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q : Finset ℕ) (k : ℕ) :
    k ∈ big n C labelled lab Q ↔ (k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧
      (∃ w ∈ Q, RR n C (n + k) w) ∧ 3 ≤ (LL n C labelled lab (n + k)).card) := by
  classical
  unfold big
  simp only [Finset.mem_filter, Finset.mem_range, bigP]

lemma big_mono (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (Q Q' : Finset ℕ) (h : Q ⊆ Q') :
    big n C labelled lab Q ⊆ big n C labelled lab Q' := by
  intro i hi
  obtain ⟨h1, h2, ⟨w, hw, hr⟩, h3⟩ := (mem_big n C labelled lab Q i).1 hi
  exact (mem_big n C labelled lab Q' i).2 ⟨h1, h2, ⟨w, h hw, hr⟩, h3⟩

lemma count (n : ℕ) (C : Circuit) {α : Type} (labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hnl : ∀ m ∈ labelled, m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and)
    (hlab : ∀ m ∈ labelled, (lab m).card ≤ 2) :
    ∀ (m : ℕ) (Q : Finset ℕ), (∀ w ∈ Q, w < m) → ∀ T : Finset α,
      (∀ x ∈ T, ∃ w ∈ Q, x ∈ LL n C labelled lab w) →
      T.card ≤ 2 * (Q.card + (big n C labelled lab Q).card) := by
  classical
  intro m
  induction m with
  | zero =>
    intro Q hQ T hT
    have hTe : T = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx => by
      obtain ⟨w, hw, _⟩ := hT x hx
      have := hQ w hw
      omega)
    rw [hTe, Finset.card_empty]
    exact Nat.zero_le _
  | succ m ih =>
    intro Q hQ T hT
    by_cases hm : m ∈ Q
    · have hQ0 : ∀ w ∈ Q.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hQ w (Finset.mem_of_mem_erase hw)
        omega
      have hcardQ : (Q.erase m).card + 1 = Q.card := Finset.card_erase_add_one hm
      by_cases hs : (∃ k, m = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or) ∧
          3 ≤ (LL n C labelled lab m).card
      · obtain ⟨⟨k, rfl, hs2, hs3⟩, hs4⟩ := hs
        have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hQ' : ∀ w ∈ insert a (insert b (Q.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hQ0 w h
        have hT' : ∀ x ∈ T, ∃ w ∈ insert a (insert b (Q.erase (n + k))),
            x ∈ LL n C labelled lab w := by
          intro x hx
          obtain ⟨w, hw, hxw⟩ := hT x hx
          by_cases hwk : w = n + k
          · rw [hwk] at hxw
            rcases LL_or n C labelled lab hnl k a b hs3 hin x hxw with h | h
            · exact ⟨a, Finset.mem_insert_self _ _, h⟩
            · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.2 ⟨hwk, hw⟩)), hxw⟩
        have hih := ih _ hQ' T hT'
        have hc' : (insert a (insert b (Q.erase (n + k)))).card ≤
            (Q.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (Q.erase (n + k)))
          have h2 := Finset.card_insert_le b (Q.erase (n + k))
          omega
        have hsub : big n C labelled lab (insert a (insert b (Q.erase (n + k)))) ⊆
            (big n C labelled lab Q).erase k := by
          intro i hi
          obtain ⟨h1, h2, ⟨w, hw, hr⟩, h3⟩ := (mem_big n C labelled lab _ i).1 hi
          have hle := rr_le n C (n + i) w hr
          have hwlt := hQ' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (mem_big n C labelled lab Q i).2 ⟨h1, h2, ?_, h3⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, rr_step n C k a (n + i) hs2 hs3 hma ha hr⟩
          · rw [h] at hr
            exact ⟨n + k, hm, rr_step n C k b (n + i) hs2 hs3 hmb hb hr⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ big n C labelled lab Q :=
          (mem_big n C labelled lab Q k).2
            ⟨hs2, hs3, ⟨n + k, hm, Relation.ReflTransGen.refl⟩, hs4⟩
        have hc2 : ((big n C labelled lab Q).erase k).card + 1 =
            (big n C labelled lab Q).card := Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        omega
      · have hsmall : (LL n C labelled lab m).card ≤ 2 := by
          by_cases hs' : ∃ k, m = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs', by omega⟩
          · exact LL_small_notor n C labelled lab hlab m hs'
        obtain ⟨B, hB⟩ : ∃ B : Finset α, ∀ x, x ∈ B ↔ (x ∈ T ∧ ¬ x ∈ LL n C labelled lab m) :=
          ⟨T.filter (fun x => ¬ x ∈ LL n C labelled lab m), fun x => Finset.mem_filter⟩
        have hT2 : ∀ x ∈ B, ∃ w ∈ Q.erase m, x ∈ LL n C labelled lab w := by
          intro x hx
          obtain ⟨hxT, hxn⟩ := (hB x).1 hx
          obtain ⟨w, hw, hxw⟩ := hT x hxT
          refine ⟨w, Finset.mem_erase.2 ⟨?_, hw⟩, hxw⟩
          intro hwm
          rw [hwm] at hxw
          exact hxn hxw
        have hsubT : T ⊆ LL n C labelled lab m ∪ B := by
          intro x hx
          rw [Finset.mem_union]
          by_cases hxl : x ∈ LL n C labelled lab m
          · exact Or.inl hxl
          · exact Or.inr ((hB x).2 ⟨hx, hxl⟩)
        have hun := Finset.card_union_le (LL n C labelled lab m) B
        have hcT := Finset.card_le_card hsubT
        have hih := ih _ hQ0 B hT2
        have hmono := Finset.card_le_card
          (big_mono n C labelled lab _ _ (Finset.erase_subset m Q))
        omega
    · refine ih Q (fun w hw => ?_) T hT
      have h1 := hQ w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega

theorem main_aux : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ 2 * (roots.card + {jb : ℕ | jb < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jb) r2) ∧ 3 ≤ ({x3 : α | ∃ m3 ∈ labelled, R m3 (n + jb) ∧ x3 ∈ lab m3}).ncard}.ncard) := by
  intro n C α S roots labelled lab hAO R hR hlabd hS
  subst hR
  have hcount := count n C labelled lab hAO.2.1 hAO.2.2
    (fun m hm => (hlabd m hm).1) (fun m hm => (hlabd m hm).2)
    (roots.sup id + 1) roots
    (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw)) S
    (fun a ha => by
      obtain ⟨r, hr, m1, hm1, hR1, ha1⟩ := hS a ha
      exact ⟨r, hr, (mem_LL n C labelled lab r a).2 ⟨m1, hm1, hR1, ha1⟩⟩)
  have key : ∀ (X : Set ℕ) (A B : ℕ), (∀ i, i ∈ X ↔ i ∈ big n C labelled lab roots) →
      A ≤ 2 * (B + (big n C labelled lab roots).card) → A ≤ 2 * (B + X.ncard) := by
    intro X A B hX hA
    have hXe : X = ((big n C labelled lab roots : Finset ℕ) : Set ℕ) := by
      ext i
      exact (hX i).trans Finset.mem_coe.symm
    rw [hXe, Set.ncard_coe_finset]
    exact hA
  refine key _ _ _ ?_ hcount
  intro i
  rw [Set.mem_ofPred_eq, mem_big]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [← ncard_LL]
    exact h4
  · rintro ⟨h1, h2, h3, h4⟩
    rw [← ncard_LL] at h4
    exact ⟨h1, h2, h3, h4⟩

end PEqualNP.Outside.L_meta_2406

theorem PEqualNP.Outside.L_meta_2406 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ 2 * (roots.card + {jb : ℕ | jb < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jb).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jb) r2) ∧ 3 ≤ ({x3 : α | ∃ m3 ∈ labelled, R m3 (n + jb) ∧ x3 ∈ lab m3}).ncard}.ncard) :=
  PEqualNP.Outside.L_meta_2406.main_aux
