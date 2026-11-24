import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5168

open PEqualNP.CircuitLowerBounds

def f (x1 : Fin (9 : ℕ) → Bool) : Bool := [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2

def P (c d : Fin 9) (C : Circuit) : Prop :=
  ∀ (y : Fin 9 → Bool), C.eval (List.ofFn y ++ [!y (0 : Fin 9), y c || y d]) = f y

def tau : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]

def reps : List ℕ := [1, 2, 3, 4, 6, 11, 12, 13, 14, 15, 16, 17, 21, 22, 24, 25, 26, 31, 33, 42, 61]

def sig (a b : Fin 9) : Fin 9 → Fin 9 :=
  if 9 * (a : ℕ) + (b : ℕ) ∈ reps ∨ 9 * (b : ℕ) + (a : ℕ) ∈ reps then id else tau

lemma tau_zero : tau 0 = 0 := by decide

lemma tau_inv : ∀ y : Fin 9 → Bool, f (fun i => y (tau i)) = f y := by
  decide +kernel

lemma table : ∀ a b : Fin 9, a < b →
    9 * ((sig a b a : Fin 9) : ℕ) + ((sig a b b : Fin 9) : ℕ) ∈ reps ∨
    9 * ((sig a b b : Fin 9) : ℕ) + ((sig a b a : Fin 9) : ℕ) ∈ reps := by
  decide +kernel

lemma sig_zero (a b : Fin 9) : sig a b 0 = 0 := by
  unfold sig; split_ifs
  · rfl
  · exact tau_zero

lemma sig_inv (a b : Fin 9) : ∀ y : Fin 9 → Bool, f (fun i => y (sig a b i)) = f y := by
  unfold sig; split_ifs
  · intro y; rfl
  · exact tau_inv

def m (σ : Fin 9 → Fin 9) (k : ℕ) : ℕ := if h : k < 9 then ((σ ⟨k, h⟩ : Fin 9) : ℕ) else k

lemma m_ge (σ : Fin 9 → Fin 9) (k : ℕ) (h : 9 ≤ k) : m σ k = k := by
  simp [m, show ¬k < 9 by omega]

lemma m_lt (σ : Fin 9 → Fin 9) (k : ℕ) (h : k < 9) : m σ k < 9 := by
  simp only [m, h, dite_true]; exact (σ ⟨k, h⟩).isLt

def remap (σ : Fin 9 → Fin 9) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (m σ) }

def rewire (σ : Fin 9 → Fin 9) (C : Circuit) : Circuit :=
  { gates := C.gates.map (remap σ), output := m σ C.output }

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

lemma getD_snoc (W : List Bool) (v : Bool) (k : ℕ) :
    (W ++ [v]).getD k false =
      if k < W.length then W.getD k false else if k = W.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy k W.length with h | h | h
  · simp [List.getElem?_append_left h, h]
  · subst h; simp
  · have h1 : ¬k < W.length := by omega
    have h2 : k ≠ W.length := by omega
    simp only [h1, h2, if_false]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma fold_inv (σ : Fin 9 → Fin 9) : ∀ (gs : List Gate) (W W' : List Bool),
    W.length = W'.length → 11 ≤ W.length →
    (∀ k, W'.getD (m σ k) false = W.getD k false) →
    ∀ k, ((gs.map (remap σ)).foldl stepF W').getD (m σ k) false = (gs.foldl stepF W).getD k false := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ h k; exact h k
  | cons g gs ih =>
    intro W W' hl h11 h k
    simp only [List.map_cons, List.foldl_cons]
    apply ih (stepF W g) (stepF W' (remap σ g))
    · simp [stepF, hl]
    · simp [stepF]; omega
    · intro k
      simp only [stepF]
      rw [getD_snoc, getD_snoc]
      by_cases hk : k < 9
      · have h1 := m_lt σ k hk
        simp only [show m σ k < W'.length by omega, show k < W.length by omega, if_true]
        exact h k
      · have e := m_ge σ k (by omega)
        rw [e]
        by_cases hk2 : k < W.length
        · simp only [show k < W'.length by omega, hk2, if_true]
          have := h k; rw [e] at this; exact this
        · simp only [show ¬k < W'.length by omega, hk2, if_false, ← hl]
          split_ifs
          · simp only [remap, List.map_map]
            congr 1
            apply List.map_congr_left
            intro i _
            exact h i
          · rfl

lemma inputs_inv (σ : Fin 9 → Fin 9) (h0 : σ 0 = 0) (y : Fin 9 → Bool) (u : Bool) :
    ∀ k, (List.ofFn y ++ [!y 0, u]).getD (m σ k) false =
      (List.ofFn (fun i => y (σ i)) ++ [!y (σ 0), u]).getD k false := by
  intro k
  rw [h0]
  simp only [List.getD_eq_getElem?_getD]
  by_cases hk : k < 9
  · have hm : m σ k = ((σ ⟨k, hk⟩ : Fin 9) : ℕ) := by simp [m, hk]
    rw [hm, List.getElem?_append_left (by simp), List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, dif_pos (σ ⟨k, hk⟩).isLt, dif_pos hk, Fin.eta]
  · rw [m_ge σ k (by omega)]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp

lemma transfer (σ : Fin 9 → Fin 9) (h0 : σ 0 = 0) (hf : ∀ y : Fin 9 → Bool, f (fun i => y (σ i)) = f y)
    (a b : Fin 9) (C : Circuit) (hP : P a b C) : P (σ a) (σ b) (rewire σ C) := by
  intro y
  have hx := hP (fun i => y (σ i))
  rw [hf] at hx
  rw [← hx]
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  exact fold_inv σ C.gates _ _ (by simp) (by simp) (inputs_inv σ h0 y _) C.output

lemma rewire_fan (σ : Fin 9 → Fin 9) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (rewire σ C) := by
  intro g hg
  simp only [rewire, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := h g0 hg0
  exact ⟨h1, by simpa [remap] using h2⟩

lemma rewire_size (σ : Fin 9 → Fin 9) (C : Circuit) : (rewire σ C).size = C.size := by
  simp [rewire, Circuit.size]

lemma swap (c d : Fin 9) (C : Circuit) (h : P c d C) : P d c C := by
  intro y; rw [Bool.or_comm]; exact h y

theorem main : ∀ (x3 x4 : Fin 9) (x5 : Circuit), x3 < x4 → PEqualNP.MetaComplexity.FanInTwo x5 →
    x5.size ≤ 13 → P x3 x4 x5 → ∃ (x10 : Fin 9) (x11 : Fin 9) (x12 : Circuit),
      9 * (x10 : ℕ) + (x11 : ℕ) ∈ reps ∧ PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ 13 ∧
        P x10 x11 x12 := by
  intro a b C hab hF hs hP
  have hT := transfer (sig a b) (sig_zero a b) (sig_inv a b) a b C hP
  rcases table a b hab with h | h
  · exact ⟨sig a b a, sig a b b, rewire (sig a b) C, h, rewire_fan _ _ hF,
      by rw [rewire_size]; exact hs, hT⟩
  · exact ⟨sig a b b, sig a b a, rewire (sig a b) C, h, rewire_fan _ _ hF,
      by rw [rewire_size]; exact hs, swap _ _ _ hT⟩

end PEqualNP.Outside.L_meta_5168

theorem PEqualNP.Outside.L_meta_5168 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 < x4 → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → x2 x3 x4 x5 → ∃ (x10 : Fin (9 : ℕ)) (x11 : Fin (9 : ℕ)) (x12 : PEqualNP.CircuitLowerBounds.Circuit), (9 : ℕ) * ↑x10 + ↑x11 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (21 : ℕ), (22 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (31 : ℕ), (33 : ℕ), (42 : ℕ), (61 : ℕ)] ∧ PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ x2 x10 x11 x12 := by
  exact PEqualNP.Outside.L_meta_5168.main
