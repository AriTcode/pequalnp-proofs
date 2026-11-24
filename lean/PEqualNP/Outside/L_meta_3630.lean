import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3630

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

def rho (r : ℕ → ℕ) (d : ℕ) (i : ℕ) : ℕ := if i < 11 then r i else i + d

def remap (r : ℕ → ℕ) (d : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho r d)⟩

lemma foldl_remap (r : ℕ → ℕ) (d : ℕ) (hr : ∀ i < 11, r i < 11 + d) :
    ∀ (gs : List Gate) (A S : List Bool), 11 ≤ A.length → S.length = A.length + d →
      (∀ i, S.getD (rho r d i) false = A.getD i false) →
      ∀ i, ((gs.map (remap r d)).foldl F S).getD (rho r d i) false = (gs.foldl F A).getD i false := by
  intro gs
  induction gs with
  | nil => intro A S _ _ h i; exact h i
  | cons g gs ih =>
    intro A S hA hS h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [F]; omega
    · simp [F]; omega
    · have hv : (remap r d g).op.eval ((remap r d g).inputs.map fun i => S.getD i false) =
          g.op.eval (g.inputs.map fun i => A.getD i false) := by
        simp only [remap, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact h i
      intro i
      simp only [F]
      rw [hv]
      rcases lt_trichotomy i A.length with hi | hi | hi
      · have h1 : rho r d i < S.length := by
          unfold rho; split
          · have := hr i (by assumption); omega
          · omega
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ hi, h i]
      · have h1 : rho r d i = S.length := by unfold rho; split <;> omega
        rw [h1, hi]
        simp
      · have h1 : S.length + 1 ≤ rho r d i := by unfold rho; split <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma ofFn_getD (x6 : Fin 9 → Bool) (l : List Bool) (v : Fin 9) :
    (List.ofFn x6 ++ l).getD (v : ℕ) false = x6 v := by
  rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma build (x1 : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo x1) (pre : List Gate) (d : ℕ)
    (r : ℕ → ℕ) (hr : ∀ i < 11, r i < 11 + d) (hpre : PEqualNP.MetaComplexity.FanInTwo ⟨pre, 0⟩)
    (hlen : pre.length = d + 1) (val : (Fin 9 → Bool) → Bool)
    (hS : ∀ x6 : Fin 9 → Bool, (pre.foldl F (List.ofFn x6 ++ [false])).length = 11 + d ∧
      ∀ i, (pre.foldl F (List.ofFn x6 ++ [false])).getD (rho r d i) false =
        (List.ofFn x6 ++ [x6 0 || x6 4, val x6]).getD i false) :
    ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ x1.size + (d + 1) ∧
      ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false]) =
        x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, val x6]) := by
  refine ⟨⟨pre ++ x1.gates.map (remap r d), rho r d x1.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hpre g hg
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      have := hf g' hg'
      simpa [remap] using this
  · simp [Circuit.size, hlen]; omega
  · intro x6
    obtain ⟨hl, hv⟩ := hS x6
    simp only [Circuit.eval, wires_eq, List.foldl_append]
    exact foldl_remap r d hr x1.gates _ _ (by simp) (by rw [hl]; simp) hv x1.output

lemma caseA (x1 : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo x1) (x2 : Finset (Fin 9))
    (t : ℕ) (ht : t < 11)
    (htv : ∀ x6 : Fin 9 → Bool, (List.ofFn x6 ++ [false, x6 0 || x6 4]).getD t false =
      decide (∃ x7 ∈ x2, x6 x7 = true)) :
    ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ x1.size + 1 ∧
      ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false]) =
        x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, decide (∃ x7 ∈ x2, x6 x7 = true)]) := by
  refine build x1 hf [⟨.or, [0, 4]⟩] 0 (fun i => if i < 9 then i else if i = 9 then 10 else t)
    ?_ ?_ rfl (fun x6 => decide (∃ x7 ∈ x2, x6 x7 = true)) ?_
  · intro i hi; split_ifs <;> omega
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    simp
  · intro x6
    have hS : List.foldl F (List.ofFn x6 ++ [false]) [⟨.or, [0, 4]⟩] =
        List.ofFn x6 ++ [false, x6 0 || x6 4] := by
      simp [F, GateOp.eval]
    rw [hS]
    refine ⟨by simp, ?_⟩
    intro i
    unfold rho
    dsimp only
    by_cases h11 : i < 11
    · rw [if_pos h11]
      by_cases h9 : i < 9
      · rw [if_pos h9, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by simp; omega)]
      · rw [if_neg h9]
        by_cases h99 : i = 9
        · subst h99; simp
        · rw [if_neg h99, htv x6]
          have : i = 10 := by omega
          subst this; simp
    · rw [if_neg h11, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma caseB (x1 : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo x1) (x2 : Finset (Fin 9))
    (hc : x2.card ≤ 2) :
    ∃ x5 : Circuit, PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size ≤ x1.size + 2 ∧
      ∀ x6 : Fin 9 → Bool, x5.eval (List.ofFn x6 ++ [false]) =
        x1.eval (List.ofFn x6 ++ [x6 0 || x6 4, decide (∃ x7 ∈ x2, x6 x7 = true)]) := by
  refine build x1 hf [⟨.or, [0, 4]⟩, ⟨.or, x2.toList.map Fin.val⟩] 1
    (fun i => if i < 9 then i else if i = 9 then 10 else 11)
    ?_ ?_ rfl (fun x6 => decide (∃ x7 ∈ x2, x6 x7 = true)) ?_
  · intro i hi; split_ifs <;> omega
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp
    · simpa using hc
  · intro x6
    have hany : (GateOp.or.eval ((x2.toList.map Fin.val).map
        (fun i => (List.ofFn x6 ++ [false, x6 0 || x6 4]).getD i false))) =
        decide (∃ x7 ∈ x2, x6 x7 = true) := by
      simp only [GateOp.eval, List.map_map]
      have : ∀ v : Fin 9, ((fun i => (List.ofFn x6 ++ [false, x6 0 || x6 4]).getD i false) ∘
          Fin.val) v = x6 v := fun v => ofFn_getD x6 _ v
      rw [List.map_congr_left (fun v _ => this v)]
      rw [Bool.eq_iff_iff, List.any_eq_true]
      simp
    have hS : List.foldl F (List.ofFn x6 ++ [false])
        [⟨.or, [0, 4]⟩, ⟨.or, x2.toList.map Fin.val⟩] =
        List.ofFn x6 ++ [false, x6 0 || x6 4, decide (∃ x7 ∈ x2, x6 x7 = true)] := by
      simp only [List.foldl_cons, List.foldl_nil, F]
      have h1 : GateOp.or.eval ([0, 4].map fun i => (List.ofFn x6 ++ [false]).getD i false) =
          (x6 0 || x6 4) := by simp [GateOp.eval]
      rw [h1]
      have h2 : List.ofFn x6 ++ [false] ++ [x6 0 || x6 4] = List.ofFn x6 ++ [false, x6 0 || x6 4] := by
        simp
      rw [h2, hany]
      simp
    rw [hS]
    refine ⟨by simp, ?_⟩
    intro i
    unfold rho
    dsimp only
    by_cases h11 : i < 11
    · rw [if_pos h11]
      by_cases h9 : i < 9
      · rw [if_pos h9, List.getD_append _ _ _ _ (by simp; omega),
          List.getD_append _ _ _ _ (by simp; omega)]
      · rw [if_neg h9]
        by_cases h99 : i = 9
        · subst h99; simp
        · rw [if_neg h99]
          have : i = 10 := by omega
          subst this; simp
    · rw [if_neg h11, List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3630

theorem PEqualNP.Outside.L_meta_3630 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ (x5.size ≤ x1.size + if x2.card ≤ (1 : ℕ) ∨ x2 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} then (1 : ℕ) else (2 : ℕ)) ∧ ∀ (x6 : Fin (9 : ℕ) → Bool), x5.eval (List.ofFn x6 ++ [Bool.false]) = x1.eval (List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true)]) := by
  intro x1 x2 hf hcard
  by_cases h : x2.card ≤ 1 ∨ x2 = {(0 : Fin 9), (4 : Fin 9)}
  · rw [if_pos h]
    rcases h with h | h
    · obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp h
      rcases Finset.subset_singleton_iff.mp hv with rfl | rfl
      · exact PEqualNP.Outside.L_meta_3630.caseA x1 hf ∅ 9 (by omega) (fun x6 => by simp)
      · exact PEqualNP.Outside.L_meta_3630.caseA x1 hf {v} v (by omega)
          (fun x6 => by rw [PEqualNP.Outside.L_meta_3630.ofFn_getD]; simp)
    · subst h
      exact PEqualNP.Outside.L_meta_3630.caseA x1 hf _ 10 (by omega) (fun x6 => by simp)
  · rw [if_neg h]
    exact PEqualNP.Outside.L_meta_3630.caseB x1 hf x2 hcard
