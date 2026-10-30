import Mathlib.Data.Set.Basic
/-! # 様相論理 演習問題 -/
open Set
namespace myModal

section

inductive formula (P : Type u) where
  | atom : P → formula P
  | falsum : formula P
  | imp : formula P → formula P → formula P
  | box : formula P → formula P
prefix:99 "#" => formula.atom
notation:100 "⊥" => formula.falsum
infixr:95 " -> " => formula.imp
prefix:98 "□" => formula.box
variable {P : Type u}

def not : formula P → formula P := fun φ => φ -> ⊥
prefix:98 "~" => not
def or : formula P → formula P → formula P := fun φ ψ => ~φ -> ψ
infixl:96 " || " => or
def and : formula P → formula P → formula P := fun φ ψ => ~(φ -> ~ψ)
infixl:97 " && " => and
def dia : formula P → formula P := fun φ => ~□~φ
prefix:98 "◇" => dia
def iff : formula P → formula P → formula P := fun φ ψ => (φ -> ψ) && (ψ -> φ)
infix:94 " <-> " => iff

--  1. 意味論

structure frame where
  world : Type
  rel : world → world → Prop
  nonempty : Nonempty world
abbrev valuation P (F : frame) := P → F.world → Prop
structure model (P : Type u) extends frame where
  val : valuation P toframe

def satisfy {M : model P} (w : M.world) : formula P → Prop
  | formula.atom p => M.val p w
  | formula.falsum => False
  | formula.imp φ ψ => satisfy w φ → satisfy w ψ
  | formula.box φ => ∀ w' : M.world, M.rel w w' → satisfy w' φ
notation:80 w " ⊨ " φ => satisfy w φ
abbrev satisfy_m (M : model P) : formula P → Prop :=
    fun φ => ∀ w : M.world, w ⊨ φ
notation:80 M " ⊨ " φ => satisfy_m M φ
abbrev satisfy_f (F : frame) : formula P → Prop :=
    fun φ => ∀ V : valuation P F, ⟨F, V⟩ ⊨ φ
notation:80 F " ⊨ " φ => satisfy_f F φ

variable {M : model P} {w : M.world} {φ ψ θ : formula P}
@[simp] theorem satisfy_atom_iff {p : P} : (w ⊨ #p) ↔ M.val p w := by simp [satisfy]
@[simp] theorem satisfy_bot_iff : (w ⊨ ⊥) ↔ False := by simp [satisfy]
@[simp] theorem satisfy_imp_iff : (w ⊨ φ -> ψ) ↔ (w ⊨ φ) → (w ⊨ ψ) := by simp [satisfy]
@[simp] theorem satisfy_box_iff :
    (w ⊨ □φ) ↔ ∀ w' : M.world, M.rel w w' → w' ⊨ φ := by simp [satisfy]
@[simp] theorem satisfy_not_iff : (w ⊨ ~φ) ↔ ¬(w ⊨ φ) := by simp [not]
@[simp] theorem satisfy_or_iff : (w ⊨ φ || ψ) ↔ (w ⊨ φ) ∨ (w ⊨ ψ) := by
  simp [or, Classical.or_iff_not_imp_left]
@[simp] theorem satisfy_and_iff : (w ⊨ φ && ψ) ↔ (w ⊨ φ) ∧ (w ⊨ ψ) := by simp [and]
@[simp] theorem satisfy_dia_iff :
    (w ⊨ ◇φ) ↔ ∃ w' : M.world, M.rel w w' ∧ w' ⊨ φ := by simp [dia]
@[simp] theorem satisfy_iff_iff :
    (w ⊨ φ <-> ψ) ↔ ((w ⊨ φ) ↔ (w ⊨ ψ)) := by simp [iff, iff_def]

variable {F : frame}
theorem satisfy_axm1 : F ⊨ (φ -> ψ -> φ) := by
  intro _ _ h _
  exact h
theorem satisfy_axm2 : F ⊨ ((φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ) := by
  intro _ _ h1 h2 h3
  exact h1 h3 (h2 h3)
theorem satisfy_nn : F ⊨ (~~φ -> φ) := by
  intro _ _ h
  exact Classical.not_not.mp h
theorem satisfy_K : F ⊨ (□ (φ -> ψ) -> □ φ -> □ ψ) := by
  intro _ _ h1 h2 w' h
  exact h1 w' h (h2 w' h)
theorem satisfy_nec : (F ⊨ φ) → F ⊨ □φ := by
  intro h V _ w _
  exact h V w

variable {p : P}
example : ((F ⊨ □#p -> #p) ↔ (∀ w : F.world, F.rel w w)) := by
  constructor
  · intro hF w
    by_contra h
    let V : valuation P F := fun q x => x ≠ w
    refine not_and.mpr (hF V w) ⟨?_, rfl⟩
    intro x
    contrapose
    simp_all [V]
  · intro hrel _ w h
    exact h w (hrel w)

--  2. 構文論

inductive prove : formula P → Prop where
  | axm1 : ∀ φ ψ : formula P, prove (φ -> ψ -> φ)
  | axm2 : ∀ φ ψ θ : formula P, prove ((φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ)
  | nn : ∀ φ : formula P, prove (~~φ -> φ)
  | K : ∀ φ ψ : formula P, prove (□(φ -> ψ) -> □φ -> □ ψ)
  | MP : ∀ φ ψ : formula P, prove φ → prove (φ -> ψ) → prove ψ
  | nec : ∀ φ : formula P, prove φ → prove (□φ)
notation:80 "⊢ " φ => prove φ

theorem axm1 (φ ψ : formula P) : ⊢ φ -> ψ -> φ := prove.axm1 φ ψ
theorem axm2 (φ ψ θ : formula P) : ⊢ (φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ := prove.axm2 φ ψ θ
theorem nn (φ : formula P) : ⊢ ~~φ -> φ := prove.nn φ
theorem K (φ ψ : formula P) : ⊢ □(φ -> ψ) -> □φ -> □ψ := prove.K φ ψ
theorem MP : (⊢ φ) → (⊢ φ -> ψ) → ⊢ ψ := prove.MP φ ψ
theorem nec : (⊢ φ) → ⊢ □φ := prove.nec φ

theorem soundness : (⊢ φ) → ∀ F : frame, F ⊨ φ := by
  intro hφ F
  induction hφ with
  | axm1 => exact satisfy_axm1
  | axm2 => exact satisfy_axm2
  | nn => exact satisfy_nn
  | K => exact satisfy_K
  | MP _ _ _ _ h1 h2 =>
    intro M w
    exact (h2 M w) (h1 M w)
  | nec _ _ h => exact satisfy_nec h

abbrev theory (P : Type u) := Set (formula P)
variable {S T : theory P} {φ ψ θ : formula P}
inductive proveP (T : theory P) : formula P → Prop where
  | assmp : ∀ φ : formula P, φ ∈ T → proveP T φ
  | axm1 : ∀ φ ψ : formula P, proveP T (φ -> ψ -> φ)
  | axm2 : ∀ φ ψ θ : formula P, proveP T ((φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ)
  | nn : ∀ φ : formula P, proveP T (~~φ -> φ)
  | MP : ∀ φ ψ : formula P, proveP T φ → proveP T (φ -> ψ) → proveP T ψ
notation:80 T " ⊢P " φ => proveP T φ
notation:80 "⊢P " φ => proveP ∅ φ

theorem prove_PtoM : (⊢P φ) → ⊢ φ := by
  intro h
  induction h with
  | assmp _ h => exact False.elim h
  | axm1 => exact axm1 _ _
  | axm2 => exact axm2 _ _ _
  | nn => exact nn _
  | MP _ _ _ _ h1 h2 => exact MP h1 h2

section prove_Prop

theorem assmpP : φ ∈ T → T ⊢P φ := proveP.assmp φ
theorem axm1P (φ ψ : formula P) : T ⊢P φ -> ψ -> φ := proveP.axm1 φ ψ
theorem axm2P (φ ψ θ : formula P) : T ⊢P (φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ := proveP.axm2 φ ψ θ
theorem nnP (φ : formula P) : T ⊢P ~~φ -> φ := proveP.nn φ
theorem MPP : (T ⊢P φ) → (T ⊢P (φ -> ψ)) → (T ⊢P ψ) := proveP.MP φ ψ

theorem proveP_imp_self (φ : formula P) : T ⊢P φ -> φ := by
  have h1 := @axm2P P T φ (φ -> φ) φ
  have h2 := @axm1P P T φ (φ -> φ)
  have h3 := @axm1P P T φ φ
  exact MPP h3 (MPP h2 h1)
theorem proveP_to_imp (φ : formula P) : (T ⊢P ψ) → T ⊢P φ -> ψ := by
  intro h1
  exact MPP h1 (axm1P ψ φ)

theorem subset_proveP : S ⊆ T → (S ⊢P φ) → T ⊢P φ := by
  intro hST hSφ
  induction hSφ with
  | assmp φ hφ => exact assmpP (hST hφ)
  | axm1 φ ψ => exact axm1P φ ψ
  | axm2 φ ψ θ => exact axm2P φ ψ θ
  | nn φ => exact nnP φ
  | MP φ ψ _ _ hφ hφψ => exact MPP hφ hφψ

theorem deduction : (T ⊢P φ -> ψ) ↔ ((T ∪ {φ}) ⊢P ψ) := by
  constructor
  · intro h
    have hφ : (T ∪ {φ}) ⊢P φ := assmpP (Or.inr rfl)
    have hφψ : (T ∪ {φ}) ⊢P φ -> ψ :=
      subset_proveP subset_union_left h
    exact MPP hφ hφψ
  · intro h
    induction h with
    | assmp ψ h =>
      cases h with
      | inl h =>
        exact proveP_to_imp φ (assmpP h)
      | inr h =>
        rw [h]
        exact proveP_imp_self φ
    | axm1 ψ1 ψ2 => exact proveP_to_imp φ (axm1P ψ1 ψ2)
    | axm2 ψ1 ψ2 ψ3 => exact proveP_to_imp φ (axm2P ψ1 ψ2 ψ3)
    | nn ψ1 => exact proveP_to_imp φ (nnP ψ1)
    | MP θ ψ _ _ h1 h2 => exact MPP h1 (MPP h2 (axm2P φ θ ψ))

theorem proveP_imp_imp : (T ⊢P φ -> ψ) → (T ⊢P ψ -> θ) → (T ⊢P φ -> θ) := by
  intro h1 h2
  have h3 := subset_proveP (@subset_union_left _ T {φ}) h1
  have h4 := subset_proveP (@subset_union_left _ T {φ}) h2
  have h5 := @assmpP P (T ∪ {φ}) φ (Or.inr rfl)
  exact deduction.mpr (MPP (MPP h5 h3) h4)
theorem proveP_not_to_imp (ψ : formula P) : (T ⊢P ~φ) → (T ⊢P φ -> ψ) := by
  rw [deduction, not, deduction]
  intro h
  exact MPP (proveP_to_imp (~ψ) h) (nnP ψ)
theorem proveP_not_imp_not : (T ⊢P φ -> ψ) ↔ (T ⊢P ~ψ -> ~φ) := by
  constructor
  · intro h
    repeat apply deduction.mpr
    have h' : (T ∪ {~ψ} ∪ {φ}) ⊢P φ -> ψ := by
      refine subset_proveP ?_ h
      intro _ h'
      exact Or.inl (Or.inl h')
    exact MPP (MPP (assmpP (Or.inr rfl)) h') (assmpP (Or.inl (Or.inr rfl)))
  · intro h
    apply deduction.mpr (MPP (deduction.mpr ?_) (nnP ψ))
    have h' : (T ∪ {φ} ∪ {~ψ}) ⊢P ~ψ -> ~φ := by
      refine subset_proveP ?_ h
      intro x hx
      exact Or.inl (Or.inl hx)
    exact MPP (assmpP (Or.inl (Or.inr rfl))) (MPP (assmpP (Or.inr rfl)) h')
theorem proveP_imp_and_not_imp : (T ⊢P φ -> ψ) → (T ⊢P ~φ -> ψ) → (T ⊢P ψ) := by
  intro h1 h2
  have h : T ⊆ T ∪ {~ψ} := subset_union_left
  have h3 : (T ∪ {~ψ}) ⊢P ~ψ := assmpP (Or.inr rfl)
  have h4 := subset_proveP h h2
  have h5 := proveP_not_imp_not.mp (subset_proveP h h1)
  exact MPP (deduction.mpr (MPP (MPP (MPP h3 h5) h4) h3)) (nnP ψ)
theorem proveP_and : (T ⊢P φ) → (T ⊢P ψ) → (T ⊢P φ && ψ) := by
  intro hφ hψ
  have h : (T ∪ {φ -> ~ψ}) ⊢P ~ψ := by
    refine MPP ?_ (assmpP (Or.inr rfl))
    exact subset_proveP (subset_union_left) hφ
  exact deduction.mpr (MPP (subset_proveP subset_union_left hψ) h)
theorem proveP_imp_and : (T ⊢P φ -> ψ) → (T ⊢P φ -> θ) → (T ⊢P φ -> ψ && θ) := by
  repeat rw [deduction]
  intro h1 h2
  exact proveP_and h1 h2
theorem proveP_iff : (T ⊢P φ -> ψ) → (T ⊢P ψ -> φ) → (T ⊢P φ <-> ψ) := by
  intro h1 h2
  exact proveP_and h1 h2
theorem proveP_and_left : (T ⊢P φ && ψ) → (T ⊢P φ) := by
  intro h
  apply MPP (deduction.mpr ?_) (nnP φ)
  apply MPP (proveP_not_to_imp (~ψ) (assmpP (Or.inr rfl)))
  exact subset_proveP subset_union_left h
theorem proveP_and_right : (T ⊢P φ && ψ) → (T ⊢P ψ) := by
  intro h
  apply MPP (deduction.mpr ?_) (nnP ψ)
  apply MPP ?_ (subset_proveP subset_union_left h)
  exact proveP_to_imp φ (assmpP (Or.inr rfl))
theorem proveP_imp_imp_to_and_imp : (T ⊢P φ -> ψ -> θ) → (T ⊢P (φ && ψ) -> θ) := by
  intro h
  have h1 : (T ∪ {φ && ψ}) ⊢P φ && ψ := assmpP (Or.inr rfl)
  have h2 := subset_proveP (@subset_union_left _ T {φ && ψ}) h
  exact deduction.mpr (MPP (proveP_and_right h1) (MPP (proveP_and_left h1) h2))
theorem proveP_or_left : (T ⊢P φ) → (T ⊢P φ || ψ) := by
  intro h
  apply proveP_not_to_imp ψ
  rw [not, deduction]
  exact MPP (subset_proveP subset_union_left h) (assmpP (Or.inr rfl))
theorem proveP_or_right : (T ⊢P ψ) → (T ⊢P φ || ψ) := by
  intro h
  exact proveP_to_imp (~φ) h
theorem proveP_or_to : (T ⊢P φ -> θ) → (T ⊢P ψ -> θ) → (T ⊢P (φ || ψ) -> θ) := by
  intro h1 h2
  have h3 : (T ∪ {~φ -> ψ}) ⊢P ~φ -> ψ := assmpP (Or.inr rfl)
  have h4 := proveP_imp_imp h3 (subset_proveP subset_union_left h2)
  exact deduction.mpr (proveP_imp_and_not_imp (subset_proveP subset_union_left h1) h4)

theorem proveP_imp_imp_imp_imp_imp : T ⊢P (φ -> ψ) -> (ψ -> θ) -> (φ -> θ) := by
  rw [deduction, deduction]
  exact proveP_imp_imp (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_imp_imp_not_imp_not : T ⊢P (φ -> ψ) -> (~ψ -> ~φ) := by
  rw [deduction]
  exact proveP_not_imp_not.mp (assmpP (Or.inr rfl))
theorem proveP_not_imp_not_imp_imp : T ⊢P (~ψ -> ~φ) -> φ -> ψ := by
  rw [deduction]
  exact proveP_not_imp_not.mpr (assmpP (Or.inr rfl))
theorem proveP_imp_imp_and : T ⊢P φ -> ψ -> φ && ψ := by
  rw [deduction, deduction]
  exact proveP_and (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_imp_imp_imp_imp_imp_and : T ⊢P (φ -> ψ) -> (φ -> θ) -> (φ -> ψ && θ) := by
  rw [deduction, deduction]
  exact proveP_imp_and (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_imp_imp_imp_imp_iff : T ⊢P (φ -> ψ) -> (ψ -> φ) -> (φ <-> ψ) := by
  rw [deduction, deduction]
  exact proveP_iff (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_and_imp_left : T ⊢P (φ && ψ) -> φ := by
  rw [deduction]
  exact proveP_and_left (assmpP (Or.inr rfl))
theorem proveP_and_imp_right : T ⊢P (φ && ψ) -> ψ := by
  rw [deduction]
  exact proveP_and_right (assmpP (Or.inr rfl))
theorem proveP_imp_imp_imp_and_imp : T ⊢P (φ -> ψ -> θ) -> (φ && ψ) -> θ := by
  rw [deduction]
  exact proveP_imp_imp_to_and_imp (assmpP (Or.inr rfl))
theorem proveP_imp_or_left : T ⊢P φ -> φ || ψ := by
  rw [deduction]
  exact proveP_or_left (assmpP (Or.inr rfl))
theorem proveP_imp_or_right : T ⊢P ψ -> φ || ψ := by
  rw [deduction]
  exact proveP_or_right (assmpP (Or.inr rfl))
theorem proveP_imp_imp_imp_imp_or_imp : T ⊢P (φ -> θ) -> (ψ -> θ) -> (φ || ψ) -> θ := by
  rw [deduction, deduction]
  exact proveP_or_to (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_not_or_imp : T ⊢P ~(φ || ψ) -> ~φ && ~ψ := by
  apply proveP_imp_and
  · exact proveP_not_imp_not.mp proveP_imp_or_left
  · exact proveP_not_imp_not.mp proveP_imp_or_right
theorem proveP_not_and_not_imp : T ⊢P (~φ && ~ψ) -> ~(φ || ψ) := by
  apply proveP_imp_imp_to_and_imp (deduction.mpr ?_)
  apply proveP_not_imp_not.mp (deduction.mpr ?_)
  exact MPP (assmpP (Or.inl (Or.inr rfl))) (assmpP (Or.inr rfl))
theorem proveP_not_and_imp : T ⊢P ~(φ && ψ) -> ~φ || ~ψ := by
  let T' := (T ∪ {~(φ && ψ)} ∪ {ψ} ∪ {φ})
  have h1 : T' ⊢P ~(φ && ψ) := assmpP (Or.inl (Or.inl (Or.inr rfl)))
  have h2 : T' ⊢P ψ := assmpP (Or.inl (Or.inr rfl))
  have h3 : T' ⊢P φ := assmpP (Or.inr rfl)
  apply deduction.mpr (proveP_not_imp_not.mp ?_)
  repeat apply deduction.mpr
  exact MPP h2 (MPP h3 (MPP h1 (nnP (φ -> ~ψ))))
theorem proveP_not_or_not_imp : T ⊢P (~φ || ~ψ) -> ~(φ && ψ) := by
  refine proveP_or_to ?_ ?_
  · exact proveP_not_imp_not.mp proveP_and_imp_left
  · exact proveP_not_imp_not.mp proveP_and_imp_right

end prove_Prop

theorem prove_imp_imp_imp_imp_imp : ⊢ (φ -> ψ) -> (ψ -> θ) -> (φ -> θ) :=
  prove_PtoM proveP_imp_imp_imp_imp_imp
theorem prove_imp_imp_not_imp_not : ⊢ (φ -> ψ) -> (~ψ -> ~φ) :=
  prove_PtoM proveP_imp_imp_not_imp_not
theorem prove_imp_imp_and : ⊢ φ -> ψ -> φ && ψ :=
  prove_PtoM proveP_imp_imp_and
theorem prove_imp_imp_imp_imp_imp_and : ⊢ (φ -> ψ) -> (φ -> θ) -> (φ -> ψ && θ) :=
  prove_PtoM proveP_imp_imp_imp_imp_imp_and
theorem prove_imp_imp_imp_imp_iff : ⊢ (φ -> ψ) -> (ψ -> φ) -> (φ <-> ψ) :=
  prove_PtoM proveP_imp_imp_imp_imp_iff
theorem prove_and_imp_left : ⊢ (φ && ψ) -> φ :=
  prove_PtoM proveP_and_imp_left
theorem prove_and_imp_right : ⊢ (φ && ψ) -> ψ :=
  prove_PtoM proveP_and_imp_right
theorem prove_imp_imp_imp_and_imp : ⊢ (φ -> ψ -> θ) -> (φ && ψ) -> θ :=
  prove_PtoM proveP_imp_imp_imp_and_imp
theorem prove_imp_or_left : ⊢ φ -> φ || ψ :=
  prove_PtoM proveP_imp_or_left
theorem prove_imp_or_right : ⊢ ψ -> φ || ψ :=
  prove_PtoM proveP_imp_or_right
theorem prove_imp_imp_imp_imp_or_imp : ⊢ (φ -> θ) -> (ψ -> θ) -> (φ || ψ) -> θ :=
  prove_PtoM proveP_imp_imp_imp_imp_or_imp
theorem prove_not_or_imp : ⊢ ~(φ || ψ) -> ~φ && ~ψ :=
  prove_PtoM proveP_not_or_imp
theorem prove_not_and_not_imp : ⊢ (~φ && ~ψ) -> ~(φ || ψ) :=
  prove_PtoM proveP_not_and_not_imp
theorem prove_not_and_imp : ⊢ ~(φ && ψ) -> ~φ || ~ψ :=
  prove_PtoM proveP_not_and_imp
theorem prove_not_or_not_imp : ⊢ (~φ || ~ψ) -> ~(φ && ψ) :=
  prove_PtoM proveP_not_or_not_imp

theorem prove_imp_to_box_imp : (⊢ φ -> ψ) → ⊢ □φ -> □ψ := by
  intro h
  exact MP (nec h) (K φ ψ)
theorem prove_imp_imp_to_box_imp_imp : (⊢ φ -> ψ -> θ) → ⊢ □φ -> □ψ -> □θ := by
  intro h
  have h1 := prove_imp_to_box_imp h
  exact MP (K ψ θ) (MP h1 prove_imp_imp_imp_imp_imp)
theorem prove_box_and : ⊢ □(φ && ψ) <-> □φ && □ψ := by
  refine MP ?_ (MP ?_ prove_imp_imp_imp_imp_iff)
  · refine MP ?_ prove_imp_imp_imp_and_imp
    exact prove_imp_imp_to_box_imp_imp prove_imp_imp_and
  · refine MP ?_ (MP ?_ prove_imp_imp_imp_imp_imp_and)
    · exact prove_imp_to_box_imp prove_and_imp_right
    · exact prove_imp_to_box_imp prove_and_imp_left

end

variable {P : Type u} {p : P} {F : frame} {φ ψ θ : formula P}

--  問1

example : (F ⊨ φ -> ψ) → F ⊨ □φ -> □ψ := sorry
example : (F ⊨ φ -> ψ -> θ) → F ⊨ □φ -> □ψ -> □θ := sorry
example : (F ⊨ φ -> ψ) → F ⊨ ◇φ -> ◇ψ := sorry
example : F ⊨ □(φ && ψ) <-> □φ && □ψ := sorry
example : F ⊨ (□φ || □ψ) -> □(φ || ψ) := sorry
example : F ⊨ ◇(φ || ψ) <-> ◇φ || ◇ψ := sorry
example : F ⊨ ◇(φ && ψ) -> ◇φ && ◇ψ := sorry

--  問2

example : (F ⊨ #p -> □◇#p) ↔ (∀ w x : F.world, F.rel w x → F.rel x w) := sorry
example : (F ⊨ □#p -> □□#p) ↔ (∀ w x y : F.world, F.rel w x → F.rel x y → F.rel w y) := sorry
example : (F ⊨ ◇#p -> □◇#p) ↔ (∀ w x y : F.world, F.rel w x → F.rel w y → F.rel x y) := sorry
example : (F ⊨ □#p -> ◇#p) ↔ (∀ w : F.world, ∃ x : F.world, F.rel w x) := sorry
example : (F ⊨ ◇□#p -> □◇#p) ↔
    (∀ w x y : F.world, F.rel w x → F.rel w y → ∃ z : F.world, F.rel x z ∧ F.rel y z) := sorry

--  問3

theorem prove_imp_to_dia_imp : (⊢ φ -> ψ) → ⊢ ◇φ -> ◇ψ := sorry
theorem prove_box_or : ⊢ (□φ || □ψ) -> □(φ || ψ) := sorry
theorem prove_dia_or : ⊢ ◇(φ || ψ) <-> ◇φ || ◇ψ := sorry
theorem prove_dia_and : ⊢ ◇(φ && ψ) -> ◇φ && ◇ψ := sorry

end myModal
