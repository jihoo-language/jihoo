import Jihoo.NativeEnvironmentWellFormed

/-! A value projection for ghost denotation, separate from native conversion
and heap execution. Only well-shaped Strict/Free nodes discard their first
operand; malformed shapes and every other native operator are retained. -/
namespace Jihoo.NativeKernel.Environment.Semantics.ValueErasure

def emit (op : Op) (arguments : List Term) : Term :=
  match op,arguments with
  | .strict,[_,result] => result
  | .free,[_,result] => result
  | _,_ => .node op arguments

mutual
  def erase : Term → Term
    | .var index => .var index
    | .node op arguments => emit op (eraseArgs arguments)
  termination_by term => sizeOf term

  def eraseArgs : List Term → List Term
    | [] => []
    | term :: rest => erase term :: eraseArgs rest
  termination_by terms => sizeOf terms
end

theorem eraseArgs_map (arguments : List Term) : eraseArgs arguments = arguments.map erase := by
  induction arguments with
  | nil => simp only [eraseArgs,List.map_nil]
  | cons argument rest ih => simp only [eraseArgs,List.map_cons,ih]

private theorem emit_rename (op : Op) (arguments : List Term) (ρ : Nat → Nat) :
    (emit op arguments).rename ρ = emit op (renameArgs op ρ 0 arguments) := by
  cases op <;> try simp [emit,Term.rename]
  all_goals
    cases arguments with
    | nil => simp [Term.rename,renameArgs]
    | cons first rest =>
      cases rest with
      | nil => simp [Term.rename,renameArgs,Op.binders,liftRenaming]
      | cons second rest =>
        cases rest with
        | nil => simp [renameArgs,Op.binders,liftRenaming]
        | cons third rest => simp [Term.rename,renameArgs,Op.binders,liftRenaming]

theorem erase_rename (term : Term) (ρ : Nat → Nat) : erase (term.rename ρ) = (erase term).rename ρ := by
  induction term using Term.rec
    (motive_2 := fun arguments => ∀ op offset ρ,
      eraseArgs (renameArgs op ρ offset arguments) = renameArgs op ρ offset (eraseArgs arguments)) generalizing ρ with
  | var => simp only [Term.rename,erase]
  | node op arguments ih =>
    simp only [Term.rename,erase]
    rw [ih,emit_rename]
  | nil => intros; simp only [renameArgs,eraseArgs]
  | cons first rest ihfirst ihrest =>
    rename_i op offset ρ
    simp only [renameArgs,eraseArgs,ihfirst,ihrest]

theorem erase_liftSub (σ : Nat → Term) (count : Nat) :
    (fun index => erase (liftSub count σ index)) = liftSub count (fun index => erase (σ index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    funext index
    cases index with
    | zero => simp only [liftSub,liftSubOne,erase]
    | succ index =>
      change erase ((liftSub count σ index).rename Nat.succ) =
        (liftSub count (fun index => erase (σ index)) index).rename Nat.succ
      rw [erase_rename,congrFun ih index]

private theorem emit_subst (op : Op) (arguments : List Term) (σ : Nat → Term) :
    (emit op arguments).subst σ = emit op (substArgs op σ 0 arguments) := by
  cases op <;> try simp [emit,Term.subst]
  all_goals
    cases arguments with
    | nil => simp [Term.subst,substArgs]
    | cons first rest =>
      cases rest with
      | nil => simp [Term.subst,substArgs,Op.binders,liftSub]
      | cons second rest =>
        cases rest with
        | nil => simp [substArgs,Op.binders,liftSub]
        | cons third rest => simp [Term.subst,substArgs,Op.binders,liftSub]

/-- Simultaneous capture-avoiding substitution commutes with value erasure on
all native syntax, including every hidden binder edge and malformed node. -/
theorem erase_subst (term : Term) (σ : Nat → Term) :
    erase (term.subst σ) = (erase term).subst (fun index => erase (σ index)) := by
  induction term using Term.rec
    (motive_2 := fun arguments => ∀ op offset σ,
      eraseArgs (substArgs op σ offset arguments) =
        substArgs op (fun index => erase (σ index)) offset (eraseArgs arguments)) generalizing σ with
  | var => simp only [Term.subst,erase]
  | node op arguments ih =>
    simp only [Term.subst,erase]
    rw [ih,emit_subst]
  | nil => intros; simp only [substArgs,eraseArgs]
  | cons first rest ihfirst ihrest =>
    rename_i op offset σ
    simp only [substArgs,eraseArgs,ihfirst,erase_liftSub,ihrest]

theorem erase_single (argument : Term) :
    (fun index => erase (single argument index)) = single (erase argument) := by
  funext index
  cases index <;> simp only [single,erase]

theorem erase_instantiate (body argument : Term) :
    erase (body.subst (single argument)) = (erase body).subst (single (erase argument)) := by
  rw [erase_subst,erase_single]

theorem erase_strict (first result : Term) : erase (.strict first result) = erase result := by
  simp only [Term.strict,erase,eraseArgs,emit]

theorem erase_free (owner result : Term) : erase (.free owner result) = erase result := by
  simp only [Term.free,erase,eraseArgs,emit]

private theorem emit_congruence (op : Op)
    (related : Conversion.ListRel ACU.Conv first second) : ACU.Conv (emit op first) (emit op second) := by
  cases op <;> try exact .node _ related
  all_goals
    cases related with
    | nil => exact .refl _
    | cons first rest =>
      cases rest with
      | nil => exact .node _ (.cons first .nil)
      | cons second rest =>
        cases rest with
        | nil => exact second
        | cons third rest => exact .node _ (.cons first (.cons second (.cons third rest)))

/-- Every existing native computational equation survives value erasure.
This is a homomorphism theorem; Strict/Free equations are not added to Conv. -/
theorem legacy_conversion (converted : NativeKernel.Conversion.Conv first second) : ACU.Conv (erase first) (erase second) := by
  induction converted using NativeKernel.Conversion.Conv.rec
    (motive_2 := fun first second _ => Conversion.ListRel ACU.Conv (eraseArgs first) (eraseArgs second)) with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op children ih => simpa only [erase] using emit_congruence op ih
  | beta erased domain body argument =>
    simpa only [erase,eraseArgs,emit,erase_instantiate] using
      (ACU.Conv.legacy (.beta erased (erase domain) (erase body) (erase argument)))
  | add first second bound =>
    simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.add first second bound))
  | sub first second proof ordered bound =>
    simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.sub first second (erase proof) ordered bound))
  | read count elements index proof value selected =>
    simpa only [erase,eraseArgs,emit] using
      (ACU.Conv.legacy (.read count (eraseArgs elements) index (erase proof) (erase value)
        (by rw [eraseArgs_map,List.getElem?_map,selected]; rfl)))
  | witnessPack predicate value proof =>
    simpa only [erase,eraseArgs,emit] using
      (ACU.Conv.legacy (.witnessPack (erase predicate) (erase value) (erase proof)))
  | proofPack predicate value proof =>
    simpa only [erase,eraseArgs,emit] using
      (ACU.Conv.legacy (.proofPack (erase predicate) (erase value) (erase proof)))
  | derefBorrow value => simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.derefBorrow (erase value)))
  | borrowDeref value => simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.borrowDeref (erase value)))
  | transportRefl family value proof =>
    simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.transportRefl (erase family) (erase value) (erase proof)))
  | ifLtTrue first second yes no bound =>
    simpa only [erase,eraseArgs,emit,erase_instantiate] using
      (ACU.Conv.legacy (.ifLtTrue first second (erase yes) (erase no) bound))
  | ifLtFalse first second yes no bound =>
    simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.ifLtFalse first second (erase yes) (erase no) bound))
  | ifEqTrue value yes no =>
    simpa only [erase,eraseArgs,emit,erase_instantiate] using (ACU.Conv.legacy (.ifEqTrue value (erase yes) (erase no)))
  | ifEqFalse first second yes no different =>
    simpa only [erase,eraseArgs,emit] using (ACU.Conv.legacy (.ifEqFalse first second (erase yes) (erase no) different))
  | nil => simp only [eraseArgs]; exact .nil
  | cons first rest ihfirst ihrest => simpa only [eraseArgs] using Conversion.ListRel.cons ihfirst ihrest

theorem acu_conversion (converted : ACU.Conv first second) : ACU.Conv (erase first) (erase second) := by
  induction converted using ACU.Conv.rec
    (motive_2 := fun first second _ => Conversion.ListRel ACU.Conv (eraseArgs first) (eraseArgs second)) with
  | legacy converted => exact legacy_conversion converted
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | node op children ih => simpa only [erase] using emit_congruence op ih
  | assoc first second third => simpa only [erase,eraseArgs,emit] using ACU.Conv.assoc (erase first) (erase second) (erase third)
  | comm first second => simpa only [erase,eraseArgs,emit] using ACU.Conv.comm (erase first) (erase second)
  | zero first => simpa only [erase,eraseArgs,emit] using ACU.Conv.zero (erase first)
  | nil => simp only [eraseArgs]; exact .nil
  | cons first rest ihfirst ihrest => simpa only [eraseArgs] using Conversion.ListRel.cons ihfirst ihrest

/-- Delta expansion is performed in the genuine admitted environment first;
no well-formedness of a fabricated erased environment is assumed. -/
def project (env : Environment) (term : Term) : Term := erase (EnvironmentDelta.expand env term)

theorem project_renaming (admissible : EnvironmentDelta.Admissible env) (term : Term) (ρ : Nat → Nat) :
    project env (term.rename ρ) = (project env term).rename ρ := by
  rw [project,EnvironmentDelta.expand_renaming admissible,erase_rename]
  rfl

theorem project_substitution (admissible : EnvironmentDelta.Admissible env) (term : Term) (σ : Nat → Term) :
    project env (term.subst σ) = (project env term).subst (fun index => project env (σ index)) := by
  rw [project,EnvironmentDelta.expand_substitution admissible,erase_subst]
  rfl

/-- All actual delta/beta/ACU conversion on all native syntax has a coherent
value projection. The theorem needs neither source recognition nor a supplied
normalization, realization, raw regularity or parallel-preservation premise. -/
theorem basis_conversion (admissible : EnvironmentDelta.Admissible env)
    (converted : EnvironmentDelta.Basis.Conv env first second) :
    ACU.Conv (project env first) (project env second) :=
  acu_conversion (converted.toProjected admissible)

theorem project_variable (env : Environment) (index : Nat) : project env (.var index) = .var index := by
  simp only [project,EnvironmentDelta.expand,erase]

theorem project_ordinary_node (ordinary : GlobalEnvironment.ordinary op = true) (arguments : List Term) :
    project env (.node op arguments) = emit op (arguments.map (project env)) := by
  rw [project,EnvironmentDelta.expand_ordinary ordinary,erase,eraseArgs_map,EnvironmentDelta.expandArgs_map,List.map_map]
  rfl

theorem project_strict (env : Environment) (first result : Term) : project env (.strict first result) = project env result := by
  rw [Term.strict,project_ordinary_node (by rfl)]
  rfl

theorem project_free (env : Environment) (owner result : Term) : project env (.free owner result) = project env result := by
  rw [Term.free,project_ordinary_node (by rfl)]
  rfl

theorem project_pi (env : Environment) (erased : Bool) (domain body : Term) :
    project env (.pi erased domain body) = .pi erased (project env domain) (project env body) := by
  rw [Term.pi,project_ordinary_node (by rfl)]
  rfl

theorem project_application (env : Environment) (function argument : Term) :
    project env (.app function argument) = .app (project env function) (project env argument) := by
  rw [Term.app,project_ordinary_node (by rfl)]
  rfl

end Jihoo.NativeKernel.Environment.Semantics.ValueErasure
