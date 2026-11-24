import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4889

abbrev inc (x1 x2 : Fin 13) : Prop := (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]

def X2 (x2 : Fin 26 → Bool) : Prop :=
  ∃ (x3 : Fin 13) (x4 : Fin 13), inc x3 x4 ∧ x2 (Fin.castAdd 13 x3) = true ∧
    x2 (Fin.natAdd 13 x4) = true

def X3 (x3 x4 : Finset (Fin 13)) (x5 : Fin 26) : Bool :=
  if ↑x5 < (13 : ℕ) then decide (Fin.ofNat 13 ↑x5 ∈ x3) else decide (Fin.ofNat 13 ↑x5 ∈ x4)

def X4 (x4 : Finset (Fin 13)) : Finset (Fin 13) := {x5 : Fin 13 | ∀ x6 ∈ x4, ¬inc x6 x5}

lemma sym (a b : Fin 13) : inc a b ↔ inc b a := by
  simp only [inc, Nat.add_comm]

lemma uniq : ∀ a s b c : Fin 13, a ≠ s → inc a b → inc s b → inc a c → inc s c → b = c := by
  decide +kernel

lemma deg : ∀ a : Fin 13, (Finset.univ.filter (fun b => inc a b)).card = 4 := by
  decide +kernel

lemma avoid (a : Fin 13) (S : Finset (Fin 13)) (hS : S.card ≤ 3) (ha : a ∉ S) :
    ∃ b, inc a b ∧ ∀ s ∈ S, ¬inc s b := by
  by_contra h
  push Not at h
  choose! f hfS hf using h
  have inj : Set.InjOn f ((Finset.univ.filter (fun b => inc a b) : Finset (Fin 13)) : Set (Fin 13)) := by
    intro b hb c hc hbc
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hb hc
    have hb' := hf b hb
    have hc' := hf c hc
    rw [hbc] at hb'
    exact uniq a (f c) b c (fun e => ha (e ▸ hfS c hc)) hb hb' hc hc'
  have hcard := Finset.card_le_card_of_injOn f
    (by intro b hb; exact hfS b (by simpa using hb)) inj
  rw [deg] at hcard
  omega

lemma X3_pt (S T : Finset (Fin 13)) (a : Fin 13) :
    X3 S T (Fin.castAdd 13 a) = decide (a ∈ S) := by
  have h1 : ((Fin.castAdd 13 a : Fin 26) : ℕ) < 13 := a.isLt
  have h2 : Fin.ofNat 13 ((Fin.castAdd 13 a : Fin 26) : ℕ) = a :=
    Fin.ext (by simp only [Fin.val_ofNat, Fin.val_castAdd]; omega)
  unfold X3
  rw [if_pos h1, h2]

lemma X3_ln (S T : Finset (Fin 13)) (b : Fin 13) :
    X3 S T (Fin.natAdd 13 b) = decide (b ∈ T) := by
  have h1 : ¬((Fin.natAdd 13 b : Fin 26) : ℕ) < 13 := by
    simp only [Fin.val_natAdd]; omega
  have h2 : Fin.ofNat 13 ((Fin.natAdd 13 b : Fin 26) : ℕ) = b :=
    Fin.ext (by simp only [Fin.val_ofNat, Fin.val_natAdd]; omega)
  unfold X3
  rw [if_neg h1, h2]

lemma cover (i : Fin 26) : (∃ a : Fin 13, i = Fin.castAdd 13 a) ∨ ∃ b : Fin 13, i = Fin.natAdd 13 b := by
  rcases i with ⟨v, hv⟩
  by_cases h : v < 13
  · exact Or.inl ⟨⟨v, h⟩, rfl⟩
  · exact Or.inr ⟨⟨v - 13, by omega⟩, Fin.ext (by simp; omega)⟩

lemma le_iff (y z : Fin 26 → Bool) : y ≤ z ↔ ∀ i, y i = true → z i = true := by
  simp only [Pi.le_def, Bool.le_iff_imp]

lemma minimal (p l : Fin 13) (h : inc p l) : Minimal X2 (X3 {p} {l}) := by
  refine ⟨⟨p, l, h, by rw [X3_pt]; simp, by rw [X3_ln]; simp⟩, ?_⟩
  intro y hy hle
  rw [le_iff] at hle ⊢
  obtain ⟨a, b, -, ya, yb⟩ := hy
  have ha := hle _ ya
  have hb := hle _ yb
  simp only [X3_pt, X3_ln, decide_eq_true_eq, Finset.mem_singleton] at ha hb
  subst ha hb
  intro i hi
  rcases cover i with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · simp only [X3_pt, decide_eq_true_eq, Finset.mem_singleton] at hi
    subst hi; exact ya
  · simp only [X3_ln, decide_eq_true_eq, Finset.mem_singleton] at hi
    subst hi; exact yb

lemma maximal1 (S : Finset (Fin 13)) (hS : S.card ≤ 3) :
    Maximal (fun y => ¬X2 y) (X3 S (X4 S)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, hab, ya, yb⟩
    simp only [X3_pt, X3_ln, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ,
      true_and] at ya yb
    exact yb a ya hab
  · intro y hy hle
    rw [le_iff] at hle ⊢
    intro i hi
    by_contra hz
    apply hy
    rcases cover i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · simp only [X3_pt, decide_eq_true_eq] at hz
      obtain ⟨b, hab, hb⟩ := avoid a S hS hz
      refine ⟨a, b, hab, hi, hle _ ?_⟩
      simp only [X3_ln, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb
    · simp only [X3_ln, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall, not_not] at hz
      obtain ⟨s, hs, hsb⟩ := hz
      refine ⟨s, b, hsb, hle _ ?_, hi⟩
      simp only [X3_pt, decide_eq_true_eq]
      exact hs

lemma maximal2 (S : Finset (Fin 13)) (hS : S.card ≤ 3) :
    Maximal (fun y => ¬X2 y) (X3 (X4 S) S) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, b, hab, ya, yb⟩
    simp only [X3_pt, X3_ln, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ,
      true_and] at ya yb
    exact ya b yb ((sym a b).mp hab)
  · intro y hy hle
    rw [le_iff] at hle ⊢
    intro i hi
    by_contra hz
    apply hy
    rcases cover i with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · simp only [X3_pt, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ, true_and,
        not_forall, not_not] at hz
      obtain ⟨s, hs, hsa⟩ := hz
      refine ⟨a, s, (sym s a).mp hsa, hi, hle _ ?_⟩
      simp only [X3_ln, decide_eq_true_eq]
      exact hs
    · simp only [X3_ln, decide_eq_true_eq] at hz
      obtain ⟨a, hba, ha⟩ := avoid b S hS hz
      refine ⟨a, b, (sym b a).mp hba, hle _ ?_, hi⟩
      simp only [X3_pt, decide_eq_true_eq, X4, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ha

theorem main : (∀ (x5 x6 : Fin 13), inc x5 x6 → Minimal X2 (X3 {x5} {x6})) ∧
    ∀ (x5 : Finset (Fin 13)), x5.card ≤ 3 →
      Maximal (fun y => ¬X2 y) (X3 x5 (X4 x5)) ∧ Maximal (fun y => ¬X2 y) (X3 (X4 x5) x5) :=
  ⟨minimal, fun S hS => ⟨maximal1 S hS, maximal2 S hS⟩⟩

end PEqualNP.Outside.L_meta_4889

theorem PEqualNP.Outside.L_meta_4889 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x1 x6 x5}; (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → Minimal x2 (x3 {x5} {x6})) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 x5 (x4 x5)) ∧ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 (x4 x5) x5) := by
  exact PEqualNP.Outside.L_meta_4889.main
