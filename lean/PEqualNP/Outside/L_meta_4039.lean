import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4039

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

lemma len_foldl (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, F]; simp; omega

lemma getD_F (w : List Bool) (g : Gate) (i : ℕ) : (F w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold F
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma pref (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ i (by simp [F]; omega), getD_F, if_pos h]

lemma gateval (gs : List Gate) : ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
    (gs.foldl F w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pref gs (F w g) w.length (by simp [F]), getD_F, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [pref gs (F w g) i (by simp [F]; omega), getD_F, if_pos h]
      · rw [List.getD_eq_default _ _ (by omega)]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have h1 := ih (F w g) k (by simpa using hk)
      have hl : (F w g).length = w.length + 1 := by simp [F]
      rw [hl] at h1
      rw [show w.length + (k + 1) = w.length + 1 + k by omega, h1]

lemma mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, w.length = w'.length →
      (∀ i, w.getD i false = true → w'.getD i false = true) →
      ∀ i, (gs.foldl F w).getD i false = true → (gs.foldl F w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ h; exact h
  | cons g gs ih =>
    intro w w' hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [F, hl])
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
      rcases hg g (by simp) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval, List.all_map,
        List.any_map, List.all_eq_true, List.any_eq_true, Function.comp, id]
      · intro hall a ha; exact h a (hall a ha)
      · rintro ⟨a, ha, hv⟩; exact ⟨a, ha, h a hv⟩
    intro i hi
    rw [getD_F] at hi ⊢
    rw [← hl]
    split_ifs at hi ⊢ with h1 h2
    all_goals first | exact h i hi | exact hv hi

lemma ofFn_getD' {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_4039

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4039 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 →     have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x5]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 ∈ x4))).getD (x1 + x5) Bool.false = Bool.true;     ∀ (x5 : Finset (Fin x1)), x4 x5 → ∃ x7 ⊆ x5, x7.card ≤ (2 : ℕ) ∧ x4 x7 := by
  intro n C hmono x4 S hS
  classical
  have hand_or : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hmono g hg).1; simpa using this
  have hlenI : ∀ T : Finset (Fin n), (List.ofFn fun v : Fin n => decide (v ∈ T)).length = n := by simp
  have hmonoW : ∀ T U : Finset (Fin n), T ⊆ U → ∀ i,
      (C.gates.foldl PEqualNP.Outside.L_meta_4039.F (List.ofFn fun v : Fin n => decide (v ∈ T))).getD i false = true →
      (C.gates.foldl PEqualNP.Outside.L_meta_4039.F (List.ofFn fun v : Fin n => decide (v ∈ U))).getD i false = true := by
    intro T U hTU
    apply PEqualNP.Outside.L_meta_4039.mono C.gates hand_or _ _ (by simp)
    intro i hi
    rw [PEqualNP.Outside.L_meta_4039.ofFn_getD'] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp only [decide_eq_true_eq] at hi ⊢; exact hTU hi
  let W : Finset (Fin n) → List Bool := fun T =>
    C.gates.foldl PEqualNP.Outside.L_meta_4039.F (List.ofFn fun v : Fin n => decide (v ∈ T))
  let Q : ℕ → Prop := fun j => ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧ (W S).getD (n + j) false = true
  have hQ : ∃ j, Q j := by
    obtain ⟨j, g, h1, h2, h3⟩ := hS
    exact ⟨j, g, h1, h2, h3⟩
  have hj0 := Nat.find_spec hQ
  have hmin : ∀ k < Nat.find hQ, ¬ Q k := fun k hk => Nat.find_min hQ hk
  set j0 := Nat.find hQ with hj0def
  have claim : ∀ i, i < n + j0 → (W S).getD i false = true →
      ∃ T ⊆ S, T.card ≤ 1 ∧ (W T).getD i false = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
    intro hi hv
    by_cases hin : i < n
    · have hp : ∀ T : Finset (Fin n), (W T).getD i false = decide ((⟨i, hin⟩ : Fin n) ∈ T) := by
        intro T
        show (C.gates.foldl PEqualNP.Outside.L_meta_4039.F (List.ofFn fun v : Fin n => decide (v ∈ T))).getD i false = _
        rw [PEqualNP.Outside.L_meta_4039.pref _ _ _ (by rw [hlenI]; exact hin),
          PEqualNP.Outside.L_meta_4039.ofFn_getD', dif_pos hin]
      rw [hp] at hv
      refine ⟨{⟨i, hin⟩}, ?_, by simp, ?_⟩
      · simpa using hv
      · rw [hp]; simp
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk0 : k < j0 := by omega
      by_cases hkl : k < C.gates.length
      · have hval : ∀ T : Finset (Fin n), (W T).getD (n + k) false =
            (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
              if i < n + k then (W T).getD i false else false) := by
          intro T
          have := PEqualNP.Outside.L_meta_4039.gateval C.gates
            (List.ofFn fun v : Fin n => decide (v ∈ T)) k hkl
          rw [hlenI] at this
          exact this
        rcases hand_or (C.gates[k]) (List.getElem_mem hkl) with hop | hop
        · exact absurd ⟨C.gates[k], by simp [hkl], hop, hv⟩ (hmin k hk0)
        · have hv' := hv
          rw [hval, hop] at hv'
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv'
          obtain ⟨i', hi'in, hi'v⟩ := hv'
          split_ifs at hi'v with hlt
          obtain ⟨T, hTS, hTc, hTv⟩ := ih i' (by omega) (by omega) hi'v
          refine ⟨T, hTS, hTc, ?_⟩
          rw [hval, hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
          exact ⟨i', hi'in, by rw [if_pos hlt]; exact hTv⟩
      · exfalso
        have : (W S).getD (n + k) false = false := List.getD_eq_default _ _
          (by show (C.gates.foldl PEqualNP.Outside.L_meta_4039.F (List.ofFn fun v : Fin n => decide (v ∈ S))).length ≤ n + k; rw [PEqualNP.Outside.L_meta_4039.len_foldl, hlenI]; omega)
        rw [this] at hv; exact Bool.false_ne_true hv
  obtain ⟨g, hg, hop, hv⟩ := hj0
  have hkl : j0 < C.gates.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hg; cases hg
  have hgk : C.gates[j0] = g := by
    rw [List.getElem?_eq_getElem hkl] at hg; exact Option.some.inj hg
  have hgmem : g ∈ C.gates := hgk ▸ List.getElem_mem hkl
  have hval : ∀ T : Finset (Fin n), (W T).getD (n + j0) false =
      g.op.eval (g.inputs.map fun i => if i < n + j0 then (W T).getD i false else false) := by
    intro T
    have := PEqualNP.Outside.L_meta_4039.gateval C.gates
      (List.ofFn fun v : Fin n => decide (v ∈ T)) j0 hkl
    rw [hlenI, hgk] at this
    exact this
  have hv' := hv
  rw [hval, hop] at hv'
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hv'
  have hT : ∀ x ∈ g.inputs, x < n + j0 ∧ ∃ T ⊆ S, T.card ≤ 1 ∧ (W T).getD x false = true := by
    intro x hx
    have := hv' x hx
    split_ifs at this with hlt
    exact ⟨hlt, claim x hlt this⟩
  have hl2 : g.inputs.length ≤ 2 := (hmono g hgmem).2
  have fin : ∀ T : Finset (Fin n), (∀ x ∈ g.inputs, x < n + j0 ∧ (W T).getD x false = true) →
      x4 T := by
    intro T hx
    refine ⟨j0, g, hg, hop, ?_⟩
    show (W T).getD (n + j0) false = true
    rw [hval, hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro x hxm
    obtain ⟨h1, h2⟩ := hx x hxm
    rw [if_pos h1]; exact h2
  match hins : g.inputs, hl2 with
  | [], _ =>
    exact ⟨∅, by simp, by simp, fin ∅ (by intro x hx; rw [hins] at hx; simp at hx)⟩
  | [a], _ =>
    obtain ⟨ha, Ta, hTaS, hTac, hTav⟩ := hT a (by rw [hins]; simp)
    exact ⟨Ta, hTaS, by omega, fin Ta (by
      intro x hx; rw [hins] at hx; simp at hx; subst hx; exact ⟨ha, hTav⟩)⟩
  | [a, b], _ =>
    obtain ⟨ha, Ta, hTaS, hTac, hTav⟩ := hT a (by rw [hins]; simp)
    obtain ⟨hb, Tb, hTbS, hTbc, hTbv⟩ := hT b (by rw [hins]; simp)
    refine ⟨Ta ∪ Tb, Finset.union_subset hTaS hTbS,
      le_trans (Finset.card_union_le _ _) (by omega), fin _ ?_⟩
    intro x hx
    rw [hins] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨ha, hmonoW Ta _ Finset.subset_union_left _ hTav⟩
    · exact ⟨hb, hmonoW Tb _ Finset.subset_union_right _ hTbv⟩
  | _ :: _ :: _ :: _, h => simp at h
