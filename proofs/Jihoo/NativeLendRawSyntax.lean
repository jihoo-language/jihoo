import Jihoo.NativeFamilyIotaValueMaps

/-! Unconditional raw Core Lend macro expansion. This syntax operation is
separate from dependent source checking and makes no claim about typing its
intermediate desugared callbacks. -/
namespace Jihoo.NativeKernel.Environment.RawLend

def lendTerm (owner reader continuation : Term) : Term :=
  .node .lend [owner,reader,continuation]

def desugar (owner reader continuation : Term) : Term :=
  .app (.app continuation (.app reader (.borrow owner))) owner

def rebuild (op : Op) (children : List Term) : Term :=
  match op,children with
  | .lend,[owner,reader,continuation] => desugar owner reader continuation
  | _,_ => .node op children

mutual
  def unlend : Term → Term
    | .var x => .var x
    | .node op children => rebuild op (unlendArgs children)
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf;all_goals omega

  def unlendArgs : List Term → List Term
    | [] => []
    | term::terms => unlend term::unlendArgs terms
  termination_by terms => sizeOf terms
  decreasing_by all_goals simp_wf;all_goals omega
end

theorem unlendArgs_map (children : List Term) : unlendArgs children = children.map unlend := by
  induction children <;> simp_all [unlendArgs]

theorem rebuild_other (head : op ≠ .lend) : rebuild op children = .node op children := by
  cases op <;> simp_all [rebuild]

theorem unlend_other (head : op ≠ .lend) :
    unlend (.node op children) = .node op (children.map unlend) := by
  rw [unlend,rebuild_other head,unlendArgs_map]

theorem unlend_lend (owner reader continuation : Term) :
    unlend (lendTerm owner reader continuation) = desugar (unlend owner) (unlend reader) (unlend continuation) := by
  simp only [lendTerm,unlend,unlendArgs,rebuild]

theorem unlend_desugar (owner reader continuation : Term) :
    unlend (desugar owner reader continuation) = desugar (unlend owner) (unlend reader) (unlend continuation) := by
  simp only [desugar,Term.app,Term.borrow,unlend,unlendArgs,rebuild]

theorem rebuild_rename (op : Op) (children : List Term) (ρ : Nat → Nat) :
    (rebuild op children).rename ρ = rebuild op (renameArgs op ρ 0 children) := by
  by_cases head : op = .lend
  · subst op
    cases children with
    | nil => simp only [rebuild,Term.rename,renameArgs]
    | cons owner rest => cases rest with
      | nil => simp only [rebuild,Term.rename,renameArgs]
      | cons reader rest => cases rest with
        | nil => simp only [rebuild,Term.rename,renameArgs]
        | cons continuation rest => cases rest with
          | nil => simp only [rebuild,desugar,Term.app,Term.borrow,Term.rename,renameArgs,Op.binders,liftRenaming]
          | cons extra rest => simp only [rebuild,Term.rename,renameArgs,Op.binders,liftRenaming]
  · rw [rebuild_other head,rebuild_other head]
    simp only [Term.rename]

theorem rebuild_subst (op : Op) (children : List Term) (σ : Nat → Term) :
    (rebuild op children).subst σ = rebuild op (substArgs op σ 0 children) := by
  by_cases head : op = .lend
  · subst op
    cases children with
    | nil => simp only [rebuild,Term.subst,substArgs]
    | cons owner rest => cases rest with
      | nil => simp only [rebuild,Term.subst,substArgs]
      | cons reader rest => cases rest with
        | nil => simp only [rebuild,Term.subst,substArgs]
        | cons continuation rest => cases rest with
          | nil => simp only [rebuild,desugar,Term.app,Term.borrow,Term.subst,substArgs,Op.binders,liftSub]
          | cons extra rest => simp only [rebuild,Term.subst,substArgs,Op.binders,liftSub]
  · rw [rebuild_other head,rebuild_other head]
    simp only [Term.subst]

theorem unlend_rename (term : Term) (ρ : Nat → Nat) :
    unlend (term.rename ρ) = (unlend term).rename ρ := by
  induction term using Term.rec
    (motive_2 := fun children => ∀ op offset ρ,
      unlendArgs (renameArgs op ρ offset children) = renameArgs op ρ offset (unlendArgs children)) generalizing ρ with
  | var => simp only [Term.rename,unlend]
  | node op children ih =>
      simp only [Term.rename,unlend]
      rw [ih,rebuild_rename]
  | nil => intros;simp only [renameArgs,unlendArgs]
  | cons term terms head tail =>
      intros
      simp only [renameArgs,unlendArgs,head,tail]

private theorem unlend_liftSub (depth : Nat) (σ : Nat → Term) :
    (fun x => unlend (liftSub depth σ x)) = liftSub depth (fun x => unlend (σ x)) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext x
      cases x with
      | zero => simp only [liftSub,liftSubOne,unlend]
      | succ x =>
          simp only [liftSub,liftSubOne,unlend_rename]
          exact congrArg (fun term => term.rename Nat.succ) (congrFun ih x)

theorem unlend_subst (term : Term) (σ : Nat → Term) :
    unlend (term.subst σ) = (unlend term).subst (fun x => unlend (σ x)) := by
  induction term using Term.rec
    (motive_2 := fun children => ∀ op offset σ,
      unlendArgs (substArgs op σ offset children) = substArgs op (fun x => unlend (σ x)) offset (unlendArgs children)) generalizing σ with
  | var => simp only [Term.subst,unlend]
  | node op children ih =>
      simp only [Term.subst,unlend]
      rw [ih,rebuild_subst]
  | nil => intros;simp only [substArgs,unlendArgs]
  | cons term terms head tail =>
      intros
      simp only [substArgs,unlendArgs,head,tail,unlend_liftSub]

theorem unlend_instantiate (body argument : Term) :
    unlend (body.subst (single argument)) = (unlend body).subst (single (unlend argument)) := by
  rw [unlend_subst]
  congr 1
  funext x
  cases x <;> simp only [single,unlend]

theorem unlend_builders : FamilyIota.BuilderMap unlend where
  app := by intros;simp only [Term.app,unlend,unlendArgs,rebuild]
  borrow := by intros;simp only [Term.borrow,unlend,unlendArgs,rebuild]
  elim := by
    intro family motive cases scrutinee
    simp only [FamilyIota.elimTerm,unlend,rebuild,unlendArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]
  caseOf := by
    intro family motive cases scrutinee
    simp only [FamilyIota.caseTerm,unlend,rebuild,unlendArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]
  view := by
    intro recursion family motive cases scrutinee
    simp only [FamilyIota.viewTerm,unlend,rebuild,unlendArgs_map,List.map_cons,List.map_append,List.map_nil,List.length_map]
  con := by
    intro family constructor values
    rw [unlend_other (op := .con family constructor values.length) (by intro same;cases same),List.length_map]
  drop := by intros;simp only [unlend,unlendArgs,rebuild]

theorem unlend_root (step : FamilyIota.Root env term result) :
    FamilyIota.Root env (unlend term) (unlend result) := unlend_builders.root step

end Jihoo.NativeKernel.Environment.RawLend
