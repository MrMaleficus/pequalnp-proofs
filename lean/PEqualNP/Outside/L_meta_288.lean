import Mathlib

theorem L_meta_288_div {K a b i i' : ℕ} (hi : i < K) (hi' : i' < K)
    (h : K * a + i = K * b + i') : a = b ∧ i = i' := by
  have hab : a = b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt h1)
      rw [Nat.mul_succ] at this
      omega
    · have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt h1)
      rw [Nat.mul_succ] at this
      omega
  subst hab
  exact ⟨rfl, by omega⟩

theorem L_meta_288_lt {m k u v i : ℕ} (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    m + 2 * k * (u * m + v) + i < m + 2 * k * m * m := by
  have h0 := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hu)
  rw [Nat.succ_mul] at h0
  have h1 : u * m + v + 1 ≤ m * m := by omega
  have h2 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  have h3 : 2 * k * (u * m + v + 1) = 2 * k * (u * m + v) + 2 * k := by ring
  have h4 : 2 * k * (m * m) = 2 * k * m * m := by ring
  omega

theorem L_meta_288_half (k : ℕ) (P : Prop) [Decidable P] :
    (Finset.univ.filter (fun i : Fin (2 * k) => (i.val % 2 = 1 ↔ P))).card = k := by
  have key : ∀ a : ℕ, a < k → 2 * a + (if P then 1 else 0) < 2 * k := by
    intro a ha
    split_ifs <;> omega
  have h : (Finset.univ : Finset (Fin k)).card =
      (Finset.univ.filter (fun i : Fin (2 * k) => (i.val % 2 = 1 ↔ P))).card := by
    apply Finset.card_bij
      (fun (a : Fin k) _ => (⟨2 * a.val + (if P then 1 else 0), key a.val a.isLt⟩ : Fin (2 * k)))
    · intro a _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hP : P <;> simp [hP]
    · intro a₁ _ a₂ _ h
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega)
    · intro i hi
      rw [Finset.mem_filter] at hi
      have hlt := i.isLt
      refine ⟨⟨i.val / 2, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      by_cases hP : P <;> simp [hP] at hi ⊢ <;> omega
  rw [← h]
  simp

theorem L_meta_288_edges {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] :
    H.edgeSet.ncard =
      (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).card := by
  set E := Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2) with hE
  have hset : H.edgeSet = ↑(E.image fun p => s(p.1, p.2)) := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeSet, Finset.coe_image, Set.mem_image, Finset.mem_coe, hE,
        Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
      constructor
      · intro hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · subst h
          exact (H.irrefl hab).elim
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨x, y, ⟨_, hxy⟩, he⟩
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn]
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
  simp only [Finset.coe_filter, hE, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hab hcd
  simp only at he
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (lt_asymm hab.1 hcd.1).elim

theorem PEqualNP.Outside.L_meta_288 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → (∀ x y : Fin (m + 2 * k * m * m), S.Adj x y → x ∈ F ∨ y ∈ F) ∧ F.card = T.card + k * H.edgeSet.ncard := by
  classical
  intro k m H T hk hT S hS F hF
  subst hS
  refine ⟨?_, ?_⟩
  · have key : ∀ a b : Fin (m + 2 * k * m * m), (∃ u v : Fin m, u < v ∧ H.Adj u v ∧
        ∃ i : Fin (2 * k), a.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
          ((i.val = 0 ∧ b.val = u.val) ∨
            (i.val + 1 < 2 * k ∧ b.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
            (i.val + 1 = 2 * k ∧ b.val = v.val))) → a ∈ F ∨ b ∈ F := by
      rintro a b ⟨u, v, huv, hadj, i, ha, hcase⟩
      rcases hcase with ⟨hi0, hb⟩ | ⟨hi1, hb⟩ | ⟨hi2, hb⟩
      · by_cases hu : u ∈ T
        · exact Or.inr ((hF b).2 (Or.inl ⟨u, hu, hb⟩))
        · exact Or.inl ((hF a).2 (Or.inr ⟨u, v, i, huv, hadj, ha, by simp [hu, hi0]⟩))
      · by_cases hp : (i.val % 2 = 1 ↔ u ∈ T)
        · exact Or.inl ((hF a).2 (Or.inr ⟨u, v, i, huv, hadj, ha, hp⟩))
        · refine Or.inr ((hF b).2 (Or.inr ⟨u, v, ⟨i.val + 1, hi1⟩, huv, hadj, ?_, ?_⟩))
          · show b.val = m + 2 * k * (u.val * m + v.val) + (i.val + 1)
            omega
          · show (i.val + 1) % 2 = 1 ↔ u ∈ T
            by_cases hu : u ∈ T <;> simp [hu] at hp ⊢ <;> omega
      · by_cases hu : u ∈ T
        · refine Or.inl ((hF a).2 (Or.inr ⟨u, v, i, huv, hadj, ha, ?_⟩))
          simp only [hu, iff_true]
          omega
        · have hv : v ∈ T := (hT u v hadj).resolve_left hu
          exact Or.inr ((hF b).2 (Or.inl ⟨v, hv, hb⟩))
    intro x y hxy
    rw [SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with h | h
    · exact key x y h
    · exact (key y x h).symm
  · rw [L_meta_288_edges H]
    set E := Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2) with hE
    set A := Finset.univ.filter
      (fun j : Fin (m + 2 * k * m * m) => ∃ u ∈ T, j.val = u.val) with hA
    set C : Fin m × Fin m → Finset (Fin (m + 2 * k * m * m)) := fun p => Finset.univ.filter
      (fun j => ∃ i : Fin (2 * k), j.val = m + 2 * k * (p.1.val * m + p.2.val) + i.val ∧
        (i.val % 2 = 1 ↔ p.1 ∈ T)) with hC
    have hFeq : F = A ∪ E.biUnion C := by
      ext j
      rw [hF j]
      simp only [hA, hE, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Prod.exists]
      constructor
      · rintro (h | ⟨u, v, i, huv, hadj, hj, hp⟩)
        · exact Or.inl h
        · exact Or.inr ⟨u, v, ⟨huv, hadj⟩, i, hj, hp⟩
      · rintro (h | ⟨u, v, ⟨huv, hadj⟩, i, hj, hp⟩)
        · exact Or.inl h
        · exact Or.inr ⟨u, v, i, huv, hadj, hj, hp⟩
    have hdisj : Disjoint A (E.biUnion C) := by
      rw [Finset.disjoint_left]
      intro j hjA hjB
      simp only [hA, hC, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion] at hjA hjB
      obtain ⟨u, _, hu⟩ := hjA
      obtain ⟨p, _, i, hj, _⟩ := hjB
      have := u.isLt
      omega
    have hAcard : A.card = T.card := by
      symm
      apply Finset.card_bij
        (fun (u : Fin m) _ => (⟨u.val, by have := u.isLt; omega⟩ : Fin (m + 2 * k * m * m)))
      · intro u hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, rfl⟩
      · intro u₁ _ u₂ _ h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · intro j hj
        obtain ⟨u, hu, hju⟩ := (Finset.mem_filter.mp hj).2
        exact ⟨u, hu, Fin.ext hju.symm⟩
    have hCcard : ∀ p ∈ E, (C p).card = k := by
      intro p _
      refine Eq.trans ?_ (L_meta_288_half k (p.1 ∈ T))
      symm
      apply Finset.card_bij (fun (i : Fin (2 * k)) _ =>
        (⟨m + 2 * k * (p.1.val * m + p.2.val) + i.val,
          L_meta_288_lt p.1.isLt p.2.isLt i.isLt⟩ : Fin (m + 2 * k * m * m)))
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl, (Finset.mem_filter.mp hi).2⟩
      · intro i₁ _ i₂ _ h
        have := congrArg Fin.val h
        simp only at this
        exact Fin.ext (by omega)
      · intro j hj
        obtain ⟨i, hji, hi⟩ := (Finset.mem_filter.mp hj).2
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, Fin.ext hji.symm⟩
    have hpair : (E : Set (Fin m × Fin m)).PairwiseDisjoint C := by
      intro p _ q _ hpq
      rw [Function.onFun, Finset.disjoint_left]
      intro j hjp hjq
      obtain ⟨i, hi, _⟩ := (Finset.mem_filter.mp hjp).2
      obtain ⟨i', hi', _⟩ := (Finset.mem_filter.mp hjq).2
      have h1 := L_meta_288_div (K := 2 * k) (a := p.1.val * m + p.2.val)
        (b := q.1.val * m + q.2.val) i.isLt i'.isLt (by omega)
      have hc1 := mul_comm m p.1.val
      have hc2 := mul_comm m q.1.val
      have h2 := L_meta_288_div (K := m) (a := p.1.val) (b := q.1.val) p.2.isLt q.2.isLt
        (by omega)
      exact hpq (Prod.ext (Fin.ext h2.1) (Fin.ext h2.2))
    rw [hFeq, Finset.card_union_of_disjoint hdisj, Finset.card_biUnion hpair, hAcard,
      Finset.sum_congr rfl hCcard, Finset.sum_const, smul_eq_mul]
    ring
