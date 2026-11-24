import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2549

open PEqualNP.CircuitLowerBounds

theorem getD_le {w w' : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w w') (i : ℕ) :
    w.getD i false ≤ w'.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem bool_le {a b : Bool} : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem false_le (b : Bool) : false ≤ b := by
  cases b <;> decide

theorem gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) {w w' : List Bool}
    (h : List.Forall₂ (fun a b => a ≤ b) w w') :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  rw [bool_le]
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro hx x hx'
    obtain ⟨i, hi, rfl⟩ := hx'
    exact bool_le.mp (getD_le h i) (hx _ ⟨i, hi, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, bool_le.mp (getD_le h i) hx⟩

theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w w' : List Bool, List.Forall₂ (fun a b => a ≤ b) w w' →
      List.Forall₂ (fun a b => a ≤ b)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h (List.Forall₂.cons (gate_le g (hgs g List.mem_cons_self) h) List.Forall₂.nil)

theorem eval_le (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 9 → Bool) (hxy : ∀ i : Fin 9, x i ≤ y i) :
    C.eval (List.ofFn x ++ [x 0 || x 4]) ≤ C.eval (List.ofFn y ++ [y 0 || y 4]) := by
  have hfn : List.Forall₂ (fun a b => a ≤ b) (List.ofFn x) (List.ofFn y) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp only [List.length_ofFn], fun i h1 h2 => ?_⟩
    simp only [List.get_eq_getElem, List.getElem_ofFn]
    exact hxy _
  have hor : (x 0 || x 4) ≤ (y 0 || y 4) := by
    have h0 := hxy 0
    have h4 := hxy 4
    revert h0 h4
    cases x 0 <;> cases x 4 <;> cases y 0 <;> cases y 4 <;> decide
  have htot : List.Forall₂ (fun a b => a ≤ b)
      (List.ofFn x ++ [x 0 || x 4]) (List.ofFn y ++ [y 0 || y 4]) := by
    exact List.rel_append hfn (List.Forall₂.cons hor List.Forall₂.nil)
  exact getD_le (fold_le C.gates hC _ _ htot) C.output

def mFn (m : ℕ) : Fin 9 → Bool := fun (x5 : Fin 9) => m.testBit ↑x5

def allTests : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 261, 264, 276, 288, 320, 385, 402]

def posTests : List ℕ :=
  [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def submask9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (m : ℕ) : Bool :=
  (!b0 || m.testBit 0) &&
  (!b1 || m.testBit 1) &&
  (!b2 || m.testBit 2) &&
  (!b3 || m.testBit 3) &&
  (!b4 || m.testBit 4) &&
  (!b5 || m.testBit 5) &&
  (!b6 || m.testBit 6) &&
  (!b7 || m.testBit 7) &&
  (!b8 || m.testBit 8)

def pickNeg9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : ℕ :=
  if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 42 then 42
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 50 then 50
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 69 then 69
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 104 then 104
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 116 then 116
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 138 then 138
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 201 then 201
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 208 then 208
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 261 then 261
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 276 then 276
  else if submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 385 then 385
  else 402

def target (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
   ((0 : Fin 9), (4 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
   ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)),
   ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (8 : Fin 9)), ((6 : Fin 9), (8 : Fin 9))].any
    fun (x6 : Fin 9 × Fin 9) => x x6.1 && x x6.2

def target9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Bool :=
  (b0 && b1) || ((b1 && b2) || ((b2 && b3) || ((b0 && b4) || ((b3 && b4) ||
  ((b0 && b5) || ((b1 && b6) || ((b2 && b7) || ((b5 && b7) || ((b3 && b8) ||
  ((b5 && b8) || ((b6 && b8) || false)))))))))))

theorem target_eq9 (x : Fin 9 → Bool) :
    target x = target9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) := by
  rfl

def submask (x : Fin 9 → Bool) (m : ℕ) : Bool :=
  submask9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) m

def pickNeg (x : Fin 9 → Bool) : ℕ :=
  pickNeg9 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

theorem pickNeg9_ok : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    target9 b0 b1 b2 b3 b4 b5 b6 b7 b8 = false →
      submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 (pickNeg9 b0 b1 b2 b3 b4 b5 b6 b7 b8) = true := by
  decide +kernel

theorem pickNeg_ok (x : Fin 9 → Bool) (ht : target x = false) :
    submask x (pickNeg x) = true := by
  rw [target_eq9] at ht
  exact pickNeg9_ok (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) ht

theorem bit_of_le (b bit : Bool) (h : (!b || bit) = true) : b ≤ bit := by
  cases b <;> cases bit <;> simp at h ⊢

theorem submask9_le (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) (m : ℕ)
    (h : submask9 b0 b1 b2 b3 b4 b5 b6 b7 b8 m = true) :
    (b0 ≤ m.testBit 0) ∧ (b1 ≤ m.testBit 1) ∧ (b2 ≤ m.testBit 2) ∧
    (b3 ≤ m.testBit 3) ∧ (b4 ≤ m.testBit 4) ∧ (b5 ≤ m.testBit 5) ∧
    (b6 ≤ m.testBit 6) ∧ (b7 ≤ m.testBit 7) ∧ (b8 ≤ m.testBit 8) := by
  unfold submask9 at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  exact ⟨bit_of_le _ _ h0, bit_of_le _ _ h1, bit_of_le _ _ h2,
         bit_of_le _ _ h3, bit_of_le _ _ h4, bit_of_le _ _ h5,
         bit_of_le _ _ h6, bit_of_le _ _ h7, bit_of_le _ _ h8⟩

theorem submask_le {m : ℕ} {x : Fin 9 → Bool} (h : submask x m = true) :
    ∀ i : Fin 9, x i ≤ mFn m i := by
  have ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    submask9_le (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) m h
  intro ⟨i, hi⟩
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · omega

theorem pickNeg_mem (x : Fin 9 → Bool) :
    pickNeg x ∈ allTests ∧ pickNeg x ∉ posTests := by
  unfold pickNeg pickNeg9
  split_ifs <;> decide

end PEqualNP.Outside.L_meta_2549

theorem PEqualNP.Outside.L_meta_2549 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       ∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) x4 := by
  intro C hmono hH x
  have hgates : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have h := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h
  cases ht : PEqualNP.Outside.L_meta_2549.target x with
  | false =>
    have hsub := PEqualNP.Outside.L_meta_2549.pickNeg_ok x ht
    have hle := PEqualNP.Outside.L_meta_2549.submask_le hsub
    have heval := PEqualNP.Outside.L_meta_2549.eval_le C hgates x (PEqualNP.Outside.L_meta_2549.mFn (PEqualNP.Outside.L_meta_2549.pickNeg x)) hle
    have hmem := PEqualNP.Outside.L_meta_2549.pickNeg_mem x
    have htest := hH (PEqualNP.Outside.L_meta_2549.pickNeg x) hmem.1
    have hdec : Decidable.decide (PEqualNP.Outside.L_meta_2549.pickNeg x ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = false :=
      decide_eq_false hmem.2
    rw [hdec] at htest
    change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn (PEqualNP.Outside.L_meta_2549.pickNeg x)) ++ [PEqualNP.Outside.L_meta_2549.mFn (PEqualNP.Outside.L_meta_2549.pickNeg x) 0 || PEqualNP.Outside.L_meta_2549.mFn (PEqualNP.Outside.L_meta_2549.pickNeg x) 4]) = false at htest
    rw [htest] at heval
    have hres : C.eval (List.ofFn x ++ [x 0 || x 4]) = false := by
      cases hc : C.eval (List.ofFn x ++ [x 0 || x 4]) with
      | false => rfl
      | true => rw [hc] at heval; exact absurd heval (by decide)
    rw [hres]
    exact ht.symm
  | true =>
    have h12 : C.eval (List.ofFn x ++ [x 0 || x 4]) = true := by
      have ht_any : [((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)),
                     ((0 : Fin 9), (4 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)),
                     ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)),
                     ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (8 : Fin 9)), ((6 : Fin 9), (8 : Fin 9))].any
                      (fun (x6 : Fin 9 × Fin 9) => x x6.1 && x x6.2) = true := ht
      rw [List.any_eq_true] at ht_any
      obtain ⟨e, he, he_val⟩ := ht_any
      simp only [Bool.and_eq_true] at he_val
      obtain ⟨he1, he2⟩ := he_val
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 3 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 3) x hle
        have h2 := hH 3 (by decide)
        have h3 : Decidable.decide ((3 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 3) ++ [PEqualNP.Outside.L_meta_2549.mFn 3 0 || PEqualNP.Outside.L_meta_2549.mFn 3 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 6 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 6) x hle
        have h2 := hH 6 (by decide)
        have h3 : Decidable.decide ((6 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 6) ++ [PEqualNP.Outside.L_meta_2549.mFn 6 0 || PEqualNP.Outside.L_meta_2549.mFn 6 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 12 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 12) x hle
        have h2 := hH 12 (by decide)
        have h3 : Decidable.decide ((12 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 12) ++ [PEqualNP.Outside.L_meta_2549.mFn 12 0 || PEqualNP.Outside.L_meta_2549.mFn 12 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 17 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 17) x hle
        have h2 := hH 17 (by decide)
        have h3 : Decidable.decide ((17 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 17) ++ [PEqualNP.Outside.L_meta_2549.mFn 17 0 || PEqualNP.Outside.L_meta_2549.mFn 17 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 24 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 24) x hle
        have h2 := hH 24 (by decide)
        have h3 : Decidable.decide ((24 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 24) ++ [PEqualNP.Outside.L_meta_2549.mFn 24 0 || PEqualNP.Outside.L_meta_2549.mFn 24 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 33 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 33) x hle
        have h2 := hH 33 (by decide)
        have h3 : Decidable.decide ((33 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 33) ++ [PEqualNP.Outside.L_meta_2549.mFn 33 0 || PEqualNP.Outside.L_meta_2549.mFn 33 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 66 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 66) x hle
        have h2 := hH 66 (by decide)
        have h3 : Decidable.decide ((66 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 66) ++ [PEqualNP.Outside.L_meta_2549.mFn 66 0 || PEqualNP.Outside.L_meta_2549.mFn 66 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 132 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 132) x hle
        have h2 := hH 132 (by decide)
        have h3 : Decidable.decide ((132 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 132) ++ [PEqualNP.Outside.L_meta_2549.mFn 132 0 || PEqualNP.Outside.L_meta_2549.mFn 132 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 160 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 160) x hle
        have h2 := hH 160 (by decide)
        have h3 : Decidable.decide ((160 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 160) ++ [PEqualNP.Outside.L_meta_2549.mFn 160 0 || PEqualNP.Outside.L_meta_2549.mFn 160 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 264 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 264) x hle
        have h2 := hH 264 (by decide)
        have h3 : Decidable.decide ((264 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 264) ++ [PEqualNP.Outside.L_meta_2549.mFn 264 0 || PEqualNP.Outside.L_meta_2549.mFn 264 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 288 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 288) x hle
        have h2 := hH 288 (by decide)
        have h3 : Decidable.decide ((288 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 288) ++ [PEqualNP.Outside.L_meta_2549.mFn 288 0 || PEqualNP.Outside.L_meta_2549.mFn 288 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
      · have hle : ∀ i : Fin 9, PEqualNP.Outside.L_meta_2549.mFn 320 i ≤ x i := by
          intro ⟨i, hi⟩; rcases i with _|_|_|_|_|_|_|_|_|i
          all_goals (dsimp [PEqualNP.Outside.L_meta_2549.mFn]; first
            | exact PEqualNP.Outside.L_meta_2549.false_le _
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he1)
            | exact PEqualNP.Outside.L_meta_2549.bool_le.mpr (fun _ => he2)
            | omega)
        have h1 := PEqualNP.Outside.L_meta_2549.eval_le C hgates (PEqualNP.Outside.L_meta_2549.mFn 320) x hle
        have h2 := hH 320 (by decide)
        have h3 : Decidable.decide ((320 : ℕ) ∈ [(3 : ℕ), 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]) = true := by decide
        rw [h3] at h2
        change C.eval (List.ofFn (PEqualNP.Outside.L_meta_2549.mFn 320) ++ [PEqualNP.Outside.L_meta_2549.mFn 320 0 || PEqualNP.Outside.L_meta_2549.mFn 320 4]) = true at h2
        rw [h2] at h1; exact PEqualNP.Outside.L_meta_2549.bool_le.mp h1 rfl
    rw [h12]
    exact ht.symm
