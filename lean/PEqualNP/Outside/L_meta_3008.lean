import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3008

open PEqualNP.CircuitLowerBounds

-- Pointwise order on bit lists, read through getD with default false.
def LeB (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem leB_append (w w' : List Bool) (a a' : Bool) (hl : w.length = w'.length)
    (h : LeB w w') (ha : a = true → a' = true) : LeB (w ++ [a]) (w' ++ [a']) := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [← hl]
    rcases Nat.lt_or_ge (i - w.length) 1 with h1 | h1
    · have h0 : i - w.length = 0 := by omega
      rw [h0] at hi ⊢
      simp only [List.getD_cons_zero] at hi ⊢
      exact ha hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi

theorem gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (w w' : List Bool) (h : LeB w w') :
    op.eval (l.map fun i => w.getD i false) = true →
      op.eval (l.map fun i => w'.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro H a ha
    exact h a (H a ha)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨a, ha, hw⟩
    exact ⟨a, ha, h a hw⟩

theorem fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w w' : List Bool), w.length = w'.length → LeB w w' →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').length ∧
      LeB (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' hl h; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro w w' hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · exact leB_append _ _ _ _ hl h (gate_mono g.op (hg g (List.mem_cons_self ..)) _ _ _ h)

theorem eval_mono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (h : LeB x y) : C.eval x = true → C.eval y = true := by
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg'
    have := (hC g hg').1
    simpa using this
  intro hx
  exact (fold_mono C.gates hg x y hl h).2 C.output hx

-- Bits of a list as a number, lowest bit first.
def bnat : List Bool → ℕ
  | [] => 0
  | b :: l => Nat.bit b (bnat l)

theorem bnat_testBit : ∀ (l : List Bool) (i : ℕ), (bnat l).testBit i = l.getD i false
  | [], i => by simp [bnat]
  | b :: l, 0 => by simp [bnat]
  | b :: l, i + 1 => by simp [bnat, Nat.testBit_bit_succ, bnat_testBit l i]

theorem bnat_lt : ∀ l : List Bool, bnat l < 2 ^ l.length
  | [] => by simp [bnat]
  | b :: l => by
    have := bnat_lt l
    simp only [bnat, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit_val] <;> omega

def N : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936,
  8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250,
  218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728,
  288160007407550752]

def ED : List (ℕ × ℕ) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12),
  (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
  (6, 8), (6, 9), (6, 11)]

-- The false rows 21 to 57 of the statement, as bit masks over the 14 vertices.
def FM : List ℕ := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338,
  2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288,
  9992, 10273, 10656, 12353, 13504, 14849, 16256]

def good (n : ℕ) : Bool :=
  ED.any (fun p => n.testBit p.1 && n.testBit p.2) || FM.any (fun f => n &&& f == n)

def allGood : ℕ → Bool
  | 0 => true
  | k + 1 => good k && allGood k

theorem allGood_spec : ∀ m, allGood m = true → ∀ n < m, good n = true
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero _)
  | k + 1, h, n, hn => by
    simp only [allGood, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · exact allGood_spec k h.2 n hlt
    · exact h.1

set_option maxRecDepth 100000 in
theorem allGood_ok : allGood 16384 = true := by decide +kernel

theorem FM_len : FM.length = 37 := by decide

theorem FM_link : ∀ j < 37, ∀ i < 14,
    (FM.getD j 0).testBit i = (N.getD i 0).testBit (j + 21) := by decide +kernel

theorem false_rows : ∀ j < 37, Nat.testBit 2097151 (j + 21) = false := by decide +kernel

theorem ED_bound : ∀ p ∈ ED, p.1 < 14 ∧ p.2 < 14 := by decide

theorem true_rows : ∀ p ∈ ED, ∃ k < 21, ∀ i < 14,
    (N.getD i 0).testBit k = true → i = p.1 ∨ i = p.2 := by decide +kernel

theorem N_len : N.length = 14 := by decide

theorem row_getD (k i : ℕ) :
    (List.map (fun (a : ℕ) => a.testBit k) N).getD i false = (N.getD i 0).testBit k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases h : N[i]? <;> simp

end PEqualNP.Outside.L_meta_3008

theorem PEqualNP.Outside.L_meta_3008 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : ℕ), x1.eval (List.map (fun (x4 : ℕ) => x4.testBit x3) [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]) = Nat.testBit (2097151 : ℕ) x3) → ∀ (x4 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (14 : ℕ)) (x6 : Fin (14 : ℕ)), (↑x5, ↑x6) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true := by
  open PEqualNP.Outside.L_meta_3008 in
  intro C hC H x4
  have H' : ∀ k, C.eval (List.map (fun (a : ℕ) => a.testBit k) N) = Nat.testBit 2097151 k := H
  have hED : ([((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] : List (ℕ × ℕ)) = ED := rfl
  rw [hED]
  have hl : (List.ofFn x4).length = 14 := List.length_ofFn
  have hrl : ∀ k, (List.map (fun (a : ℕ) => a.testBit k) N).length = 14 := by
    intro k; simp [N_len]
  have hlt : bnat (List.ofFn x4) < 16384 := by
    have := bnat_lt (List.ofFn x4); rw [hl] at this; simpa using this
  have hx : ∀ i : Fin 14, x4 i = (bnat (List.ofFn x4)).testBit i := by
    intro i; rw [bnat_testBit, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hbig : ∀ i, 14 ≤ i → (bnat (List.ofFn x4)).testBit i = false := by
    intro i hi
    apply Nat.testBit_eq_false_of_lt
    calc bnat (List.ofFn x4) < 16384 := hlt
      _ = 2 ^ 14 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  constructor
  · intro hev
    by_contra hne
    have hg := allGood_spec 16384 allGood_ok _ hlt
    simp only [good, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hg
    rcases hg with ⟨p, hp, h1, h2⟩ | ⟨f, hf, hand⟩
    · apply hne
      obtain ⟨b1, b2⟩ := ED_bound p hp
      refine ⟨⟨p.1, b1⟩, ⟨p.2, b2⟩, by simpa using hp, ?_, ?_⟩
      · rw [hx]; exact h1
      · rw [hx]; exact h2
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hf
      rw [FM_len] at hj
      have hle : LeB (List.ofFn x4) (List.map (fun (a : ℕ) => a.testBit (j + 21)) N) := by
        intro i hi
        rw [← bnat_testBit] at hi
        have hi14 : i < 14 := by
          by_contra hc; rw [hbig i (by omega)] at hi; exact Bool.false_ne_true hi
        have hfi : (FM[j]).testBit i = true := by
          rw [← hand, Nat.testBit_land] at hi; simp at hi; exact hi.2
        rw [row_getD, ← FM_link j hj i hi14, List.getD_eq_getElem _ _ (by rw [FM_len]; exact hj)]
        exact hfi
      have := eval_mono C hC _ _ (by rw [hl, hrl]) hle hev
      rw [H', false_rows j hj] at this
      exact Bool.false_ne_true this
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨k, hk, hrow⟩ := true_rows _ hab
    have hle : LeB (List.map (fun (c : ℕ) => c.testBit k) N) (List.ofFn x4) := by
      intro i hi
      rw [row_getD] at hi
      have hi14 : i < 14 := by
        by_contra hc
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [N_len]; omega)] at hi
        simp at hi
      rcases hrow i hi14 hi with rfl | rfl
      · rw [List.getD_eq_getElem _ _ (by simpa using hi14), List.getElem_ofFn]; exact ha
      · rw [List.getD_eq_getElem _ _ (by simpa using hi14), List.getElem_ofFn]; exact hb
    have := H' k
    have hk' : ∀ k < 21, Nat.testBit 2097151 k = true := by decide
    rw [hk' k hk] at this
    exact eval_mono C hC _ _ (by rw [hl, hrl]) hle this
