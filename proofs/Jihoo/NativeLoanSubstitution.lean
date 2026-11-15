import Jihoo.NativeLoanRenaming

/-! Simultaneous typed ghost substitution for the complete loan-indexed
judgment, retaining actual context lookup annotations. Runtime source names
may become arbitrary ghost terms after closing. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private theorem shift_subst_lift (term : Term) (σ : Nat → Term) :
    (term.rename Nat.succ).subst (liftSubOne σ) = (term.subst σ).rename Nat.succ := by
  rw [Term.subst_rename, Term.rename_subst]
  rfl

namespace Ghost
/-- Each substituted variable is independently typed at its transformed
actual lookup annotation. No output term derivation is supplied. -/
def Substitution (env : Environment) (Γ Δ : Context) (σ : Nat → Term) : Prop :=
  ∀ x binding, lookup Γ x = some binding → HasType env [] Δ true (σ x) (binding.ty.subst σ)

theorem Substitution.lift (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : Substitution env Γ Δ σ) (domain : Term) (erased : Bool) :
    Substitution env (⟨domain, erased⟩ :: Γ) (⟨domain.subst σ, erased⟩ :: Δ) (liftSubOne σ) := by
  intro x binding found
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      simp only [liftSubOne, shift_subst_lift]
      exact HasType.var (b := ⟨(domain.subst σ).rename Nat.succ, erased⟩) rfl (Or.inl rfl)
  | succ x =>
      simp only [lookup] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      simpa only [liftSubOne, shift_subst_lift] using
        (typed x original selected).ghostWeaken wellFormed (domain.subst σ) erased
end Ghost

private theorem shifted_one (term : Term) :
    PartialRenaming.shift (-1) 0 (term.rename Nat.succ) = some term := by
  rw [PartialRenaming.shift_negative (by decide : (-1 : Int) < 0)]
  change PartialRenaming.lower 0 1 (term.rename Nat.succ) = some term
  simpa only [Nat.add_one] using lower_raised term 1

private theorem dependent_subst_target
    (wf : UnifiedProgram.EnvWellFormed env) (σ : Nat → Term)
    (owned : Owned env T) (domainConverted : Conversion.Conv env domain (.ref T))
    (outlived : Outlived env A) (firstConverted : Conversion.Conv env first A)
    (againConverted : Conversion.Conv env again (T.rename Nat.succ))
    (resultConverted : Conversion.Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside)
    (ownerTyped : HasType env [] Δ true (owner.subst σ) (T.subst σ))
    (domainTyped : Binder env [] Δ false (domain.subst σ) sort)
    (readerTyped : HasType env [] Δ true ((Lending.read owner readerBody).subst σ) (A.subst σ))
    (continuationTyped : HasType env [] Δ true ((Lending.restore owner first body).subst σ)
      ((Term.pi false first result).subst σ)) :
    HasType env [] Δ true
      ((Term.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))).subst σ)
      (outside.subst σ) := by
  have reweakens := Checker.branch_type_reweakens removed
  have converted := resultConverted.substitution (liftSubOne σ) wf.closed
  rw [← reweakens,shift_subst_lift] at converted
  have againRelated := againConverted.substitution (liftSubOne σ) wf.closed
  rw [shift_subst_lift] at againRelated
  have target := HasType.lendDependentGhost
    (owner := owner.subst σ) (T := T.subst σ) (domain := domain.subst σ) (sort := sort)
    (readerBody := readerBody.subst (liftSubOne σ)) (A := A.subst σ)
    (first := first.subst σ) (again := again.subst (liftSubOne σ))
    (body := body.subst (liftSub 2 σ)) (result := result.subst (liftSubOne σ))
    (normal := (outside.subst σ).rename Nat.succ) (outside := outside.subst σ)
    ownerTyped (owned.substitution σ wf.closed) domainTyped
    (by simpa only [subst_ref] using domainConverted.substitution σ wf.closed)
    (by simpa only [Lending.read_subst] using readerTyped)
    (outlived.substitution wf.closed σ) (firstConverted.substitution σ wf.closed) againRelated
    (by simpa only [Lending.restore_subst,Term.subst,substArgs,Op.binders,liftSub] using continuationTyped)
    converted (shifted_one _)
  simpa only [Lending.subst_lend,Term.lam,Term.subst,substArgs,Op.binders,liftSub] using target

set_option linter.unusedSimpArgs false in
private theorem substitution_rule (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) :
    ∀ Δ σ, Ghost.Substitution env ctx Δ σ → HasType env [] Δ true (term.subst σ) (type.subst σ) := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ ctx erased domain sort _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ → Binder env [] Δ erased (domain.subst σ) sort)
    (motive_2 := fun _ ctx _ term type _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ → HasType env [] Δ true (term.subst σ) (type.subst σ))
    (motive_3 := fun _ ctx _ data telescope arguments result _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ →
      Arguments env [] Δ true data (telescope.subst σ) (arguments.map (Term.subst σ)) (result.subst σ))
    (motive_4 := fun _ ctx motive signatures branches _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ →
      (∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature) →
      Cases env [] Δ (motive.subst σ) signatures (branches.map (Term.subst σ)))
    (motive_5 := fun _ ctx _ types branches _ => ∀ Δ σ, Ghost.Substitution env ctx Δ σ →
      BranchTypes env [] Δ true (types.map (Term.subst σ)) (branches.map (Term.subst σ)))
  all_goals intros
  case intro =>
    rename_i typed allowed ih_typed Δ σ hσ
    exact .intro (by simpa using ih_typed Δ σ hσ) (binderAllowed_substitution wellFormed.closed allowed σ)
  case var =>
    rename_i hx _ Δ σ hσ
    simpa only [Term.subst] using hσ _ _ hx
  case univ =>
    rename_i bound Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.univ (ctx := Δ) (ghost := true) bound)
  case prop =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.prop (ctx := Δ) (ghost := true))
  case u64 =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.u64 (ctx := Δ) (ghost := true))
  case i64 =>
    rename_i Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.i64 (ctx := Δ) (ghost := true))
  case natural =>
    rename_i bound Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.natural (ctx := Δ) (ghost := true) bound)
  case integer =>
    rename_i lo hi Δ σ hσ
    simpa [Term.subst, substArgs] using (HasType.integer (ctx := Δ) (ghost := true) lo hi)
  case array =>
    rename_i hn ih_hn Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.array (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hn Δ σ hσ)
  case lt =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.lt (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case eq =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.eq (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case pi =>
    rename_i hA hB ih_hA ih_hB Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.pi (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (by simpa using ih_hB _ _ (hσ.lift wellFormed _ _))
  case lam =>
    rename_i hA hb ih_hA ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.lam (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hA Δ σ hσ) (ih_hb _ _ (hσ.lift wellFormed _ _))
  case app =>
    rename_i ctx mode f e A B a hf ha allowed ih_hf ih_ha Δ σ hσ
    change HasType env [] Δ true ((Term.app f a).subst σ) ((B.subst (single a)).subst σ)
    rw [Term.subst_instantiate]
    simp only [Term.subst, substArgs, Op.binders, liftSub]
    have hf' : HasType env [] Δ true (f.subst σ)
        (.pi e (A.subst σ) (B.subst (liftSubOne σ))) := by
      simpa [Term.subst,substArgs,Op.binders,liftSub] using ih_hf Δ σ hσ
    have ha' : HasType env [] Δ (true || e) (a.subst σ) (A.subst σ) := by
      simpa using ih_ha Δ σ hσ
    exact HasType.app hf' ha' (Or.inl rfl)
  case uadd =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.uadd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case usub =>
    rename_i ha hb hp ih_ha ih_hb ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.usub (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case refl =>
    rename_i ha ih_ha Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refl (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
  case zeroLe =>
    rename_i ha ih_ha Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.zeroLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
  case decide =>
    rename_i ha hb hab Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      (HasType.decide (ctx := Δ) (ghost := true) ha hb hab)
  case decideConverted =>
    rename_i ha hb ca cb hm hn hmn ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.decideConverted (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
        (by simpa [Term.subst, substArgs] using ca.substitution σ wellFormed.closed)
        (by simpa [Term.subst, substArgs] using cb.substitution σ wellFormed.closed) hm hn hmn
  case elements =>
    rename_i n xs sourceLoans Γ mode hn hb hs ih_hs Δ σ hσ
    have ht := HasType.elements (ctx := Δ) (ghost := true)
      (xs := xs.map (Term.subst σ)) (n := n) (by simpa using hn) (by simpa using hb)
      (fun y hy => by
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
        simpa [Term.subst,substArgs] using ih_hs x hx Δ σ hσ)
    simpa [Term.subst,substArgs,Op.binders,liftSub] using ht
  case index =>
    rename_i ha hi hp ih_ha ih_hi ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.index (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hi Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case arith =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.arith (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case strict =>
    rename_i ha hb ih_ha ih_hb Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.strict (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ)
  case ltAdd =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltAdd (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case ltCancel =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltCancel (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case ltLe =>
    rename_i ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.ltLe (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hb Δ σ hσ) (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hc Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)
  case transport =>
    rename_i hf he hp ih_hf ih_he ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.transport
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hf Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_he Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case refine =>
    rename_i hp ih_hp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.refine (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
  case pack =>
    rename_i hp ha hq ih_hp ih_ha ih_hq Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.pack
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hp Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ha Δ σ hσ)
        (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hq Δ σ hσ)
  case witness =>
    rename_i hs ih_hs Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.witness (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)
  case proof =>
    rename_i hs ih_hs Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.proof (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_hs Δ σ hσ)
  case ifLt =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using
      HasType.ifLt (by simpa [Term.subst,substArgs] using iha Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihb Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihy _ _ (hσ.lift wellFormed _ true))
        (ihn Δ σ hσ)
  case ifEq =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using
      HasType.ifEq (by simpa [Term.subst,substArgs] using iha Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihb Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihy _ _ (hσ.lift wellFormed _ true))
        (ihn Δ σ hσ)
  case absurd =>
    rename_i hT hp allowed ihT ihp Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.absurd (by simpa using ihT Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihp Δ σ hσ)
        (Or.inl rfl)
  case foldI64 =>
    rename_i hn hi hb allowed ihn ihi ihb Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.foldI64 (by simpa [Term.subst,substArgs] using ihn Δ σ hσ)
        (by simpa [Term.subst,substArgs] using ihi Δ σ hσ)
        (by simpa only [foldBodyType_subst] using ihb Δ σ hσ) (Or.inl rfl)
  case loop =>
    rename_i hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb Δ σ hσ
    simpa [Term.subst,substArgs,Op.binders,liftSub] using
      HasType.loop
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihm Δ σ hσ)
        (Or.inl rfl)
        (by simpa [Term.subst,substArgs] using ihn Δ σ hσ)
        (by simpa [Term.subst,substArgs,Op.binders,liftSub] using ihi Δ σ hσ)
        (by simpa only [loopBodyType_subst,Bool.true_or] using ihb Δ σ hσ)
        (Or.inl rfl)
  case back =>
    rename_i formed owned motive allowed iho ihm Δ σ hσ
    have target := HasType.back (ghost := true)
      (by simpa [Term.subst, substArgs] using iho Δ σ hσ) (owned.substitution σ wellFormed.closed)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihm Δ σ hσ) (Or.inl rfl)
    simpa only [subst_back, Term.subst, substArgs] using target
  case give =>
    rename_i owner owned motive allowed result iho ihm ihr Δ σ hσ
    have target := HasType.give (ghost := true)
      (iho Δ σ hσ) (owned.substitution σ wellFormed.closed)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihm Δ σ hσ) (Or.inl rfl)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihr Δ σ hσ)
    simpa only [subst_give, subst_back] using target
  case take =>
    rename_i value continuation owner result converted lowered allowed ihv ihk Δ σ hσ
    have cv := owner.substitution σ wellFormed.closed
    have cp := result.substitution (liftSub 1 σ) wellFormed.closed
    rw [subst_takeResultType] at cp
    have cr := converted.substitution (liftSub 2 σ) wellFormed.closed
    rw [load_result_subst σ lowered] at cr
    have target := HasType.take (ghost := true)
      (by simpa only [subst_back] using ihv Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihk Δ σ hσ)
      cv (by simpa only [subst_takeResultType, liftSub] using cp)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa [Term.subst, substArgs, Op.binders, liftSub] using target
  case foldOwned =>
    rename_i count init owned body allowed ihc ihi ihb Δ σ hσ
    have lifted := HasType.foldOwned (ghost := true)
      (by simpa [Term.subst, substArgs] using ihc Δ σ hσ) (ihi Δ σ hσ) (owned.substitution σ wellFormed.closed)
      (by simpa only [foldAccumulatorBodyType_subst] using ihb Δ σ hσ) (Or.inl rfl)
    simpa [Term.subst, substArgs, Op.binders, liftSub] using lifted
  case dataElim =>
    rename_i family entry analysis sourceLoans ctx motive proof ghost scrutinee indices types caseTerms found isData boxed size motiveTyped scrutineeTyped generated branches allowed ihm ihs ihb Δ σ hσ
    have hm := ihm Δ σ hσ
    rw [dataMotiveType_subst] at hm
    have generated' := dataCaseTypes_subst_success (wellFormed.signatures _ _ found) generated Δ.length σ
    have lifted := HasType.dataElim (ghost := true) (ctx := Δ) (analysis := analysis)
      (proof := proof) (indices := indices.map (Term.subst σ)) found isData boxed
      (by simpa only [List.length_map] using size)
      (by simpa only [List.map_take] using hm)
      (by simpa only [Term.subst, substArgs_ind, Bool.true_or] using ihs Δ σ hσ)
      (by simpa only [List.map_take] using generated')
      (by simpa only [Bool.true_or] using ihb Δ σ hσ) (Or.inl rfl)
    cases analysis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Term.subst, apply_ite, substArgs_elim, substArgs_caseOf, List.map_cons, List.map_append,
      List.map_singleton, List.map_nil, List.length_map, applications_subst, List.map_drop,
      substArgs, Op.binders, liftSub] using lifted
  case drop =>
    rename_i found boxed owner rest iho ihr Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.drop found boxed (by simpa [Term.subst, substArgs_ind] using iho Δ σ hσ) (ihr Δ σ hσ)
  case refOwned =>
    rename_i owner owned ih Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using
      HasType.refOwned (by simpa [Term.subst, substArgs] using ih Δ σ hσ) (owned.substitution σ wellFormed.closed)
  case ghostBorrowOwned =>
    rename_i owner owned ih Δ σ hσ
    simpa only [subst_borrow, subst_ref] using HasType.ghostBorrowOwned (ih Δ σ hσ) (owned.substitution σ wellFormed.closed)
  case ghostDerefOwned =>
    rename_i reference ih Δ σ hσ
    simpa only [subst_deref, subst_ref] using
      HasType.ghostDerefOwned (by simpa only [subst_ref] using ih Δ σ hσ)
  case view =>
    rename_i family entry ctx ghost scrutinee indices motive dependent recursive types caseTerms found isData boxed arity size scrutineeTyped motiveTyped allowed generated branches ihs ihm ihb Δ σ hσ
    have generated' := viewCaseTypes_subst_success (wellFormed.signatures _ _ found) generated Δ.length σ
    have result := HasType.view (ctx := Δ) (ghost := true) (indices := indices.map (Term.subst σ))
      (dependent := dependent) (recursion := recursive) found isData boxed arity
      (by simpa only [List.length_map] using size)
      (by simpa only [subst_ref,Term.subst,substArgs_ind] using ihs Δ σ hσ)
      (by simpa only [viewMotiveType_subst,Term.subst,substArgs_ind] using ihm Δ σ hσ)
      (Or.inl rfl) generated' (ihb Δ σ hσ)
    simpa only [Term.subst,substArgs_view,List.map_cons,List.map_append,List.map_singleton,List.map_nil,
      List.length_map,viewResult_subst] using result
  case convert =>
    rename_i ht hc ih_ht Δ σ hσ
    exact .convert (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ih_ht Δ σ hσ) (hc.substitution σ wellFormed.closed)
  case global =>
    rename_i found Δ σ hσ
    have closed := (wellFormed.globals _ _ found).1
    simpa only [Term.subst, substArgs, closed_rename closed, closed_subst closed] using
      (HasType.global (ctx := Δ) (ghost := true) found)
  case ind =>
    rename_i family entry count fields sourceLoans ctx mode found arity size typedIndices ih Δ σ hσ
    have lifted := HasType.ind (ctx := Δ) (ghost := true) (xs := fields.map (Term.subst σ)) found arity
      (by simpa only [List.length_map] using size)
      (fun index member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        simpa only [Term.subst, substArgs] using ih old oldMember Δ σ hσ)
    simpa only [Term.subst, substArgs_ind, apply_ite, substArgs] using lifted
  case con =>
    rename_i family entry constructor signature count sourceLoans ctx mode fields arity indices found signatureFound size arguments ih Δ σ hσ
    have signatureScope := wellFormed.signatures _ _ found signature (List.mem_of_getElem? signatureFound)
    have closed := signatureScope.signatureTerm_scoped family
    have lifted := ih Δ σ hσ
    have arguments' : Arguments env [] Δ true entry.declaration.data
        ((signatureTerm family signature).rename (fun x => x + Δ.length))
        (fields.map (Term.subst σ)) (.node (.ind family arity) (indices.map (Term.subst σ))) := by
      simpa only [closed_rename closed, closed_subst closed, Term.subst, substArgs_ind] using lifted
    have result := HasType.con found signatureFound (by simpa only [List.length_map] using size) arguments'
    simpa only [Term.subst, substArgs_con, substArgs_ind] using result
  case propElim =>
    rename_i found isProp motiveTyped casesTyped scrutineeTyped ihm ihc ihs Δ σ hσ
    have result := HasType.propElim (ghost := true) found isProp
      (by simpa only [propMotiveType_subst] using ihm Δ σ hσ)
      (ihc Δ σ hσ (wellFormed.signatures _ _ found))
      (by simpa only [Term.subst, substArgs_ind] using ihs Δ σ hσ)
    simpa only [Term.subst, substArgs_elim, List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      List.length_map, applications_subst] using result
  case buffer =>
    rename_i typed ih Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.buffer
      (by simpa [Term.subst, substArgs] using ih Δ σ hσ)
  case alloc =>
    rename_i count value ihc ihv Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.alloc
      (by simpa [Term.subst, substArgs] using ihc Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihv Δ σ hσ)
  case store =>
    rename_i buffer index value proof ihb ihi ihv ihp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.store
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihb Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihv Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
  case load =>
    rename_i buffer index proof continuation value owner converted lowered allowed ihb ihi ihp ihk Δ σ hσ
    have hk := ihk Δ σ hσ
    have cv := value.substitution σ wellFormed.closed
    have co := owner.substitution (liftSubOne σ) wellFormed.closed
    have cr := converted.substitution (liftSub 2 σ) wellFormed.closed
    rw [load_result_subst σ lowered] at cr
    have result := HasType.load (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihb Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using hk)
      (by simpa [Term.subst, substArgs] using cv)
      (by simpa only [subst_buffer, shift_subst_lift] using co)
      cr (load_result_shifted _) (Or.inl rfl)
    simpa only [subst_load] using result
  case free =>
    rename_i buffer rest ihb ihr Δ σ hσ
    simpa only [subst_free, subst_buffer] using HasType.free
      (by simpa only [subst_buffer] using ihb Δ σ hσ) (ihr Δ σ hσ)
  case refBuffer =>
    rename_i count ih Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.refBuffer
      (by simpa [Term.subst, substArgs] using ih Δ σ hσ)
  case ghostBorrow =>
    rename_i buffer ih Δ σ hσ
    simpa only [subst_borrow, subst_ref, subst_buffer] using HasType.ghostBorrow
      (by simpa only [subst_buffer] using ih Δ σ hσ)
  case ghostDeref =>
    rename_i reference ih Δ σ hσ
    simpa only [subst_deref, subst_ref, subst_buffer] using HasType.ghostDeref
      (by simpa only [subst_ref, subst_buffer] using ih Δ σ hσ)
  case borrowedIndex =>
    rename_i reference index proof ihr ihi ihp Δ σ hσ
    simpa [Term.subst, substArgs, Op.binders, liftSub] using HasType.borrowedIndex
      (by simpa only [subst_ref, subst_buffer] using ihr Δ σ hσ)
      (by simpa [Term.subst, substArgs] using ihi Δ σ hσ)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using ihp Δ σ hσ)
  case nil =>
    rename_i converted Δ σ hσ
    simpa only [List.map_nil] using Arguments.nil (ctx := Δ) (ghost := true) (converted.substitution σ wellFormed.closed)
  case cons =>
    rename_i telescope erased domain rest sourceLoans ctx mode data argument arguments result converted typed argumentsTyped iht iha Δ σ hσ
    have tail := iha Δ σ hσ
    change Arguments env [] Δ true data ((rest.subst (single argument)).subst σ)
      (arguments.map (Term.subst σ)) (result.subst σ) at tail
    rw [Term.subst_instantiate] at tail
    have result := Arguments.cons (env := env) (ctx := Δ) (ghost := true) (data := data)
      (by simpa [Term.subst, substArgs, Op.binders, liftSub] using converted.substitution σ wellFormed.closed)
      (by simpa only [Bool.true_or] using iht Δ σ hσ) tail
    simpa only [List.map_cons] using result
  case nil => exact Cases.nil
  case cons =>
    rename_i typed branches iht ihb Δ σ hσ scopes
    have branch := iht Δ σ hσ
    rw [propCaseType_subst (scopes _ (by simp))] at branch
    exact Cases.cons branch (ihb Δ σ hσ (fun signature member => scopes signature (by simp [member])))
  case nil => exact BranchTypes.nil
  case cons =>
    rename_i typed branches iht ihb Δ σ hσ
    simpa only [List.map_cons] using BranchTypes.cons (iht Δ σ hσ) (ihb Δ σ hσ)

  case codeBorrowOwned =>
    rename_i source owned active ih Δ σ hσ
    simpa only [subst_borrow,subst_ref] using
      HasType.ghostBorrowOwned (ih Δ σ hσ) (owned.substitution σ wellFormed.closed)
  case lendGeneric =>
    rename_i ownerTyped owned outlived readerTyped continuationTyped allowed iho ihr ihc Δ σ hσ
    have target := HasType.lendGeneric (ghost := true)
      (iho Δ σ hσ) (owned.substitution σ wellFormed.closed) (outlived.substitution wellFormed.closed σ)
      (by simpa only [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihr Δ σ hσ)
      (by simpa only [Term.subst,substArgs,Op.binders,liftSub,shift_subst_lift] using ihc Δ σ hσ)
      (Or.inl rfl)
    simpa only [Lending.subst_lend] using target
  case lendDependentCode =>
    rename_i ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted
      continuationTyped converted removed allowed iho ihd ihr ihc Δ σ hσ
    exact dependent_subst_target wellFormed σ owned domainConverted outlived firstConverted againConverted
      converted removed (iho Δ σ hσ) (ihd Δ σ hσ) (ihr Δ σ hσ) (ihc Δ σ hσ)
  case lendDependentGhost =>
    rename_i ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted
      continuationTyped converted removed iho ihd ihr ihc Δ σ hσ
    exact dependent_subst_target wellFormed σ owned domainConverted outlived firstConverted againConverted
      converted removed (iho Δ σ hσ) (ihd Δ σ hσ) (ihr Δ σ hσ) (ihc Δ σ hσ)

theorem HasType.ghostSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) {Δ : Context} {σ : Nat → Term}
    (substituted : Ghost.Substitution env ctx Δ σ) : HasType env [] Δ true (term.subst σ) (type.subst σ) :=
  substitution_rule wellFormed typed Δ σ substituted

theorem Binder.ghostSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (binding : Binder env loans ctx erased domain sort) {Δ : Context} {σ : Nat → Term}
    (substituted : Ghost.Substitution env ctx Δ σ) : Binder env [] Δ erased (domain.subst σ) sort := by
  cases binding with
  | intro formed allowed =>
      exact .intro (by simpa only [SortTag.subst_term] using formed.ghostSubstitution wellFormed substituted)
        (binderAllowed_substitution wellFormed.closed allowed σ)

namespace Ghost
theorem Substitution.single (erased : Bool) (typed : HasType env loans ctx true argument domain) :
    Substitution env (⟨domain, erased⟩ :: ctx) ctx (single argument) := by
  intro x binding found
  cases x with
  | zero =>
      simp only [lookup, Option.some.injEq] at found
      cases found
      simpa only [NativeKernel.single, Term.shift_subst_single] using typed.ghost []
  | succ x =>
      simp only [lookup] at found
      obtain ⟨original, selected, same⟩ := Option.map_eq_some_iff.mp found
      subst binding
      simp only [NativeKernel.single, Term.shift_subst_single]
      exact .var selected (Or.inl rfl)
end Ghost

theorem HasType.ghostInstantiate (wellFormed : UnifiedProgram.EnvWellFormed env)
    (bodyTyped : HasType env loans (⟨domain, erased⟩ :: ctx) mode body result)
    (argumentTyped : HasType env argumentLoans ctx true argument domain) :
    HasType env [] ctx true (body.subst (single argument)) (result.subst (single argument)) :=
  bodyTyped.ghostSubstitution wellFormed (Ghost.Substitution.single erased argumentTyped)

theorem HasType.checkedGhostSubstitution
    (history : UnifiedProgram.UnifiedProgramChecked definitions familyDeclarations env)
    (typed : HasType env loans ctx mode term type) (substituted : Ghost.Substitution env ctx Δ σ) :
    HasType env [] Δ true (term.subst σ) (type.subst σ) := typed.ghostSubstitution history.wellFormed substituted


end Jihoo.NativeKernel.Environment.LoanTyping
