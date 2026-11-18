import Jihoo.NativeLoanRenaming
import Jihoo.NativeLoanFunctionInversion
import Jihoo.NativeCodePolicyRenaming

/-! Variable renaming preserves the complete Loan64 derivation in its original
mode. Source lookup types and erasure flags are retained, and active named
loans must be transported to the target slots. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

/-- A variable map transports the context and all currently active source
loans. Entered source frames stay old when descending beneath a binder. -/
structure CodeRenaming (sourceLoans : Loans.Stack) (source : Context)
    (targetLoans : Loans.Stack) (target : Context) (indices : Nat → Nat) : Prop where
  lookups : Ghost.Renaming source target indices
  entered : Loans.Entered source.length sourceLoans
  active : ∀ owner, Loans.active source.length sourceLoans owner = true →
    Loans.active target.length targetLoans (indices owner) = true

theorem CodeRenaming.lift (renamed : CodeRenaming sourceLoans source targetLoans target indices)
    (domain : Term) (erased : Bool) :
    CodeRenaming sourceLoans (⟨domain,erased⟩ :: source)
      targetLoans (⟨domain.rename indices,erased⟩ :: target) (Indexed.liftRenaming indices) := by
  refine ⟨renamed.lookups.lift domain erased,?_,?_⟩
  · intro frame member
    exact Nat.le_trans (renamed.entered frame member) (Nat.le_succ _)
  · intro index allowed
    cases index with
    | zero =>
        obtain ⟨frame,member,depth,selected⟩ := Loans.active_iff.mp allowed
        have previous := renamed.entered frame member
        simp only [List.length_cons] at selected
        omega
    | succ index =>
        have previous : Loans.active source.length sourceLoans index = true := by
          simpa only [List.length_cons,Loans.active_weaken renamed.entered] using allowed
        obtain ⟨frame,member,depth,selected⟩ := Loans.active_iff.mp (renamed.active index previous)
        apply Loans.active_iff.mpr
        simp only [List.length_cons,Indexed.liftRenaming]
        exact ⟨frame,member,by omega,by omega⟩

theorem CodeRenaming.enter (renamed : CodeRenaming sourceLoans source targetLoans target indices)
    (owner : Nat) :
    CodeRenaming (Loans.enter source.length owner sourceLoans) source
      (Loans.enter target.length (indices owner) targetLoans) target indices := by
  refine ⟨renamed.lookups,Loans.entered_enter renamed.entered,?_⟩
  intro index allowed
  rw [Loans.active_enter,Bool.or_eq_true] at allowed ⊢
  rcases allowed with same | previous
  · have same' : owner = index := by simpa only [beq_iff_eq] using same
    subst index
    exact Or.inl (by simp)
  · exact Or.inr (renamed.active index previous)

/-- The executable loan rebase supplies the required target permissions for
a context renaming, including when the renaming identifies owner aliases. -/
theorem CodeRenaming.rebase (renamed : Ghost.Renaming source target indices)
    (entered : Loans.Entered source.length sourceLoans) :
    CodeRenaming sourceLoans source (Loans.rebase source.length target.length indices sourceLoans)
      target indices :=
  ⟨renamed, entered, fun _ allowed => Loans.active_rebase allowed⟩

private theorem application_rename (allowed : applicationAllowed env mode domain argument)
    (indices : Nat → Nat) (closed : Conversion.Closed env) :
    applicationAllowed env mode (domain.rename indices) (argument.rename indices) := by
  rcases allowed with ghost | ⟨normal,converted,globals,representation⟩
  · exact Or.inl ghost
  · refine Or.inr ⟨normal.rename indices,converted.renaming indices closed,by simpa using globals,?_⟩
    rcases representation with ordinary | ⟨kind,value,convertedValue,plain⟩
    · exact Or.inl (by simpa using ordinary)
    · exact Or.inr ⟨by simpa using kind,value.rename indices,convertedValue.renaming indices closed,
        by simpa using plain⟩

private theorem code_guard_rename
    (allowed : mode = true ∨ nonFunction env term) (indices : Nat → Nat) (closed : Conversion.Closed env) :
    mode = true ∨ nonFunction env (term.rename indices) := by
  rcases allowed with ghost | ⟨normal,converted,head⟩
  · exact Or.inl ghost
  · exact Or.inr ⟨normal.rename indices,converted.renaming indices closed,by
      cases normal <;> simp_all only [Term.rename,RawLend.nonFunctionHead]⟩

private theorem iteration_motive_rename (allowed : IterationMotiveAllowed env mode proof motive)
    (indices : Nat → Nat) (closed : Conversion.Closed env) :
    IterationMotiveAllowed env mode proof (motive.rename indices) := by
  rcases allowed with ghost | proof | ⟨normal,converted,scalar⟩ | ⟨flag,domain,body,converted,owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl ⟨normal.rename indices,converted.renaming indices closed,by simpa using scalar⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨flag,domain.rename indices,body.rename (liftRenaming 1 indices),
      by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using converted.renaming indices closed,
      owned.renaming _ closed⟩))

private theorem view_motive_rename (allowed : ViewMotiveAllowed env mode dependent motive)
    (indices : Nat → Nat) (closed : Conversion.Closed env) :
    ViewMotiveAllowed env mode dependent (motive.rename indices) := by
  rcases allowed with ghost | nondependent | ⟨flag,domain,body,converted,represented⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl nondependent)
  · exact Or.inr (Or.inr ⟨flag,domain.rename indices,body.rename (liftRenaming 1 indices),
      by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming] using converted.renaming indices closed,
      Environment.viewRepresentation_rename represented indices⟩)

private theorem rename_shift_one (term : Term) (ρ : Nat → Nat) :
    (term.rename Nat.succ).rename (Indexed.liftRenaming ρ) = (term.rename ρ).rename Nat.succ := by
  rw [Term.rename_comp, Term.rename_comp]
  rfl

private theorem shifted_one (term : Term) :
    PartialRenaming.shift (-1) 0 (term.rename Nat.succ) = some term := by
  rw [PartialRenaming.shift_negative (by decide : (-1 : Int) < 0)]
  change PartialRenaming.lower 0 1 (term.rename Nat.succ) = some term
  simpa only [Nat.add_one] using lower_raised term 1

private theorem dependent_rename_target
    (wf : UnifiedProgram.EnvWellFormed env) (ρ : Nat → Nat)
    (owned : Owned env T) (domainConverted : Conversion.Conv env domain (.ref T))
    (outlived : Outlived env A) (firstConverted : Conversion.Conv env first A)
    (againConverted : Conversion.Conv env again (T.rename Nat.succ))
    (resultConverted : Conversion.Conv env result normal)
    (removed : PartialRenaming.shift (-1) 0 normal = some outside)
    (ownerTyped : HasType env targetLoans Δ true (owner.rename ρ) (T.rename ρ))
    (domainTyped : Binder env targetLoans Δ false (domain.rename ρ) sort)
    (readerTyped : HasType env targetLoans Δ true ((Lending.read owner readerBody).rename ρ) (A.rename ρ))
    (continuationTyped : HasType env targetLoans Δ true ((Lending.restore owner first body).rename ρ)
      ((Term.pi false first result).rename ρ)) :
    HasType env targetLoans Δ true
      ((Term.lend owner (.lam false domain readerBody) (.lam false first (.lam false again body))).rename ρ)
      (outside.rename ρ) := by
  have reweakens := Checker.branch_type_reweakens removed
  have converted := resultConverted.renaming (Indexed.liftRenaming ρ) wf.closed
  rw [← reweakens,rename_shift_one] at converted
  have againRelated := againConverted.renaming (Indexed.liftRenaming ρ) wf.closed
  rw [rename_shift_one] at againRelated
  have target := HasType.lendDependentGhost
    (owner := owner.rename ρ) (T := T.rename ρ) (domain := domain.rename ρ) (sort := sort)
    (readerBody := readerBody.rename (Indexed.liftRenaming ρ)) (A := A.rename ρ)
    (first := first.rename ρ) (again := again.rename (Indexed.liftRenaming ρ))
    (body := body.rename (liftRenaming 2 ρ)) (result := result.rename (Indexed.liftRenaming ρ))
    (normal := (outside.rename ρ).rename Nat.succ) (outside := outside.rename ρ)
    ownerTyped (owned.renaming ρ wf.closed) domainTyped
    (by simpa only [rename_ref] using domainConverted.renaming ρ wf.closed)
    (by simpa only [Lending.read_rename] using readerTyped)
    (outlived.renaming wf.closed ρ) (firstConverted.renaming ρ wf.closed) againRelated
    (by simpa only [Lending.restore_rename,Term.rename,renameArgs,Op.binders,liftRenaming] using continuationTyped)
    converted (shifted_one _)
  simpa only [Lending.rename_lend,Term.lam,Term.rename,renameArgs,Op.binders,liftRenaming] using target

set_option linter.unusedSimpArgs false in
private theorem code_renaming_rule (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) :
    ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
      HasType env targetLoans Δ mode (term.rename ρ) (type.rename ρ) := by
  apply HasType.rec (t := typed)
    (motive_1 := fun loans ctx erased domain sort _ =>
      ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
        Binder env targetLoans Δ erased (domain.rename ρ) sort)
    (motive_2 := fun loans ctx mode term type _ =>
      ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
        HasType env targetLoans Δ mode (term.rename ρ) (type.rename ρ))
    (motive_3 := fun loans ctx mode data telescope arguments result _ =>
      ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
        Arguments env targetLoans Δ mode data (telescope.rename ρ) (arguments.map (Term.rename ρ)) (result.rename ρ))
    (motive_4 := fun loans ctx motive signatures branches _ =>
      ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
        (∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature) →
        Cases env targetLoans Δ (motive.rename ρ) signatures (branches.map (Term.rename ρ)))
    (motive_5 := fun loans ctx mode types branches _ =>
      ∀ Δ targetLoans ρ, CodeRenaming loans ctx targetLoans Δ ρ →
        BranchTypes env targetLoans Δ mode (types.map (Term.rename ρ)) (branches.map (Term.rename ρ)))
  all_goals intros
  case intro =>
    rename_i typed allowed ih_typed Δ targetLoans ρ hρ
    exact .intro (by simpa using ih_typed Δ targetLoans ρ hρ) (binderAllowed_renaming wellFormed.closed allowed ρ)
  case var =>
    rename_i hx allowed Δ targetLoans ρ hρ
    simpa only [Term.rename] using HasType.var (hρ.lookups _ _ hx) allowed
  case univ =>
    rename_i bound Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.univ (ctx := Δ) (ghost := _) bound)
  case prop =>
    rename_i Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.prop (ctx := Δ) (ghost := _))
  case u64 =>
    rename_i Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.u64 (ctx := Δ) (ghost := _))
  case i64 =>
    rename_i Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.i64 (ctx := Δ) (ghost := _))
  case natural =>
    rename_i bound Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.natural (ctx := Δ) (ghost := _) bound)
  case integer =>
    rename_i lo hi Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.integer (ctx := Δ) (ghost := _) lo hi)
  case array =>
    rename_i hn ih_hn Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.array (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hn Δ targetLoans ρ hρ)
  case lt =>
    rename_i ha hb ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lt (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
  case eq =>
    rename_i ha hb ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.eq (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
  case pi =>
    rename_i hA hB ih_hA ih_hB Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pi (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ targetLoans ρ hρ) (by simpa using ih_hB _ _ _ (hρ.lift _ _))
  case lam =>
    rename_i hA hb ih_hA ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lam (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ targetLoans ρ hρ) (ih_hb _ _ _ (hρ.lift _ _))
  case app =>
    rename_i ctx mode f e A B a hf ha allowed ih_hf ih_ha Δ targetLoans ρ hρ
    change HasType env targetLoans Δ mode ((Term.app f a).rename ρ) ((B.subst (single a)).rename ρ)
    rw [Term.rename_instantiate]
    simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
    have hf' : HasType env targetLoans Δ mode (f.rename ρ)
        (.pi e (A.rename ρ) (B.rename (Indexed.liftRenaming ρ))) := by
      simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ih_hf Δ targetLoans ρ hρ
    have ha' : HasType env targetLoans Δ (mode || e) (a.rename ρ) (A.rename ρ) := by
      simpa using ih_ha Δ targetLoans ρ hρ
    exact HasType.app hf' ha' (application_rename allowed ρ wellFormed.closed)
  case uadd =>
    rename_i ha hb ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.uadd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
  case usub =>
    rename_i ha hb hp ih_ha ih_hb ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.usub (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case refl =>
    rename_i ha ih_ha Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.refl (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ)
  case zeroLe =>
    rename_i ha ih_ha Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.zeroLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ)
  case decide =>
    rename_i ha hb hab Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      (HasType.decide (ctx := Δ) (ghost := _) ha hb hab)
  case decideConverted =>
    rename_i ha hb ca cb hm hn hmn ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.decideConverted (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs] using ca.renaming ρ wellFormed.closed)
        (by simpa [Term.rename, renameArgs] using cb.renaming ρ wellFormed.closed) hm hn hmn
  case elements =>
    rename_i n xs sourceLoans Γ mode hn hb hs ih_hs Δ targetLoans ρ hρ
    have ht := HasType.elements (ctx := Δ) (ghost := _)
      (xs := xs.map (Term.rename ρ)) (n := n) (by simpa using hn) (by simpa using hb)
      (fun y hy => by
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
        simpa [Term.rename,renameArgs] using ih_hs x hx Δ targetLoans ρ hρ)
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ht
  case index =>
    rename_i ha hi hp ih_ha ih_hi ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.index (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hi Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case arith =>
    rename_i ha hb ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.arith (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
  case strict =>
    rename_i ha hb ih_ha ih_hb Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.strict (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ)
  case ltAdd =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltAdd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case ltCancel =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltCancel (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case ltLe =>
    rename_i ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ targetLoans ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ targetLoans ρ hρ)
  case transport =>
    rename_i hf he hp ih_hf ih_he ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.transport
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hf Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_he Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case refine =>
    rename_i hp ih_hp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.refine (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
  case pack =>
    rename_i hp ha hq ih_hp ih_ha ih_hq Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pack
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ targetLoans ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ targetLoans ρ hρ)
  case witness =>
    rename_i hs ih_hs Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.witness (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ targetLoans ρ hρ)
  case proof =>
    rename_i hs ih_hs Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.proof (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ targetLoans ρ hρ)
  case ifLt =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ targetLoans ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifLt (by simpa [Term.rename,renameArgs] using iha Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ _ (hρ.lift _ true))
        (ihn Δ targetLoans ρ hρ)
  case ifEq =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ targetLoans ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifEq (by simpa [Term.rename,renameArgs] using iha Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ _ (hρ.lift _ true))
        (ihn Δ targetLoans ρ hρ)
  case absurd =>
    rename_i hT hp allowed ihT ihp Δ targetLoans ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.absurd (by simpa using ihT Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihp Δ targetLoans ρ hρ)
        (code_guard_rename allowed ρ wellFormed.closed)
  case foldI64 =>
    rename_i hn hi hb allowed ihn ihi ihb Δ targetLoans ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.foldI64 (by simpa [Term.rename,renameArgs] using ihn Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihi Δ targetLoans ρ hρ)
        (by simpa only [foldBodyType_rename] using ihb Δ targetLoans ρ hρ)
        (Environment.IterationBodyAllowed.renaming allowed ρ)
  case loop =>
    rename_i hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb Δ targetLoans ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.loop
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihm Δ targetLoans ρ hρ)
        (iteration_motive_rename motivePolicy ρ wellFormed.closed)
        (by simpa [Term.rename,renameArgs] using ihn Δ targetLoans ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihi Δ targetLoans ρ hρ)
        (by simpa only [loopBodyType_rename] using ihb Δ targetLoans ρ hρ)
        (Environment.IterationBodyAllowed.renaming bodyPolicy ρ)
  case back =>
    rename_i formed owned motive allowed iho ihm Δ targetLoans ρ hρ
    have target := HasType.back (ghost := _)
      (by simpa [Term.rename, renameArgs] using iho Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ targetLoans ρ hρ)
      (allowed.renaming ρ wellFormed.closed)
    simpa only [rename_back, Term.rename, renameArgs] using target
  case give =>
    rename_i owner owned motive allowed result iho ihm ihr Δ targetLoans ρ hρ
    have target := HasType.give (ghost := _)
      (iho Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ targetLoans ρ hρ)
      (allowed.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ targetLoans ρ hρ)
    simpa only [rename_give, rename_back] using target
  case take =>
    rename_i value continuation owner result converted lowered allowed ihv ihk Δ targetLoans ρ hρ
    have cv := owner.renaming ρ wellFormed.closed
    have cp := result.renaming (liftRenaming 1 ρ) wellFormed.closed
    rw [rename_takeResultType] at cp
    have cr := converted.renaming (liftRenaming 2 ρ) wellFormed.closed
    rw [load_result_rename ρ lowered] at cr
    have target := HasType.take (ghost := _)
      (by simpa only [rename_back] using ihv Δ targetLoans ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihk Δ targetLoans ρ hρ)
      cv (by simpa only [rename_takeResultType, liftRenaming] using cp)
      cr (load_result_shifted _) (code_guard_rename allowed ρ wellFormed.closed)
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using target
  case foldOwned =>
    rename_i count init owned body allowed ihc ihi ihb Δ targetLoans ρ hρ
    have lifted := HasType.foldOwned (ghost := _)
      (by simpa [Term.rename, renameArgs] using ihc Δ targetLoans ρ hρ) (ihi Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa only [foldAccumulatorBodyType_rename] using ihb Δ targetLoans ρ hρ)
      (Environment.IterationBodyAllowed.renaming allowed ρ)
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using lifted
  case dataElim =>
    rename_i family entry analysis sourceLoans ctx motive proof ghost scrutinee indices types caseTerms found isData boxed size motiveTyped scrutineeTyped generated branches allowed ihm ihs ihb Δ targetLoans ρ hρ
    have hm := ihm Δ targetLoans ρ hρ
    rw [dataMotiveType_rename] at hm
    have generated' := dataCaseTypes_rename_success (wellFormed.signatures _ _ found) generated Δ.length ρ
    have lifted := HasType.dataElim (ghost := _) (ctx := Δ) (analysis := analysis)
      (proof := proof) (indices := indices.map (Term.rename ρ)) found isData boxed
      (by simpa only [List.length_map] using size)
      (by simpa only [List.map_take] using hm)
      (by simpa only [Term.rename, renameArgs_ind] using ihs Δ targetLoans ρ hρ)
      (by simpa only [List.map_take] using generated')
      (by simpa using ihb Δ targetLoans ρ hρ)
      (by simpa only [continuationAllowed,Term.app,Term.rename,renameArgs,Op.binders,liftRenaming,
        applications_rename,List.map_drop]
        using code_guard_rename allowed ρ wellFormed.closed)
    cases analysis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Term.rename, apply_ite, renameArgs_elim, renameArgs_caseOf, List.map_cons, List.map_append,
      List.map_singleton, List.map_nil, List.length_map, applications_rename, List.map_drop,
      renameArgs, Op.binders, liftRenaming] using lifted
  case drop =>
    rename_i found boxed owner rest iho ihr Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.drop found boxed (by simpa [Term.rename, renameArgs_ind] using iho Δ targetLoans ρ hρ) (ihr Δ targetLoans ρ hρ)
  case refOwned =>
    rename_i owner owned ih Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.refOwned (by simpa [Term.rename, renameArgs] using ih Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
  case ghostBorrowOwned =>
    rename_i owner owned ih Δ targetLoans ρ hρ
    simpa only [rename_borrow, rename_ref] using HasType.ghostBorrowOwned (ih Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
  case ghostDerefOwned =>
    rename_i reference ih Δ targetLoans ρ hρ
    simpa only [rename_deref, rename_ref] using
      HasType.ghostDerefOwned (by simpa only [rename_ref] using ih Δ targetLoans ρ hρ)
  case view =>
    rename_i family entry ctx ghost scrutinee indices motive dependent recursive types caseTerms found isData boxed arity size scrutineeTyped motiveTyped allowed generated branches ihs ihm ihb Δ targetLoans ρ hρ
    have generated' := viewCaseTypes_rename_success (wellFormed.signatures _ _ found) generated Δ.length ρ
    have result := HasType.view (ctx := Δ) (ghost := _) (indices := indices.map (Term.rename ρ))
      (dependent := dependent) (recursion := recursive) found isData boxed arity
      (by simpa only [List.length_map] using size)
      (by simpa only [rename_ref,Term.rename,renameArgs_ind] using ihs Δ targetLoans ρ hρ)
      (by simpa only [viewMotiveType_rename,Term.rename,renameArgs_ind] using ihm Δ targetLoans ρ hρ)
      (view_motive_rename allowed ρ wellFormed.closed) generated' (ihb Δ targetLoans ρ hρ)
    simpa only [Term.rename,renameArgs_view,List.map_cons,List.map_append,List.map_singleton,List.map_nil,
      List.length_map,viewResult_rename] using result
  case convert =>
    rename_i ht hc ih_ht Δ targetLoans ρ hρ
    exact .convert (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ht Δ targetLoans ρ hρ) (hc.renaming ρ wellFormed.closed)
  case global =>
    rename_i found Δ targetLoans ρ hρ
    have closed := (wellFormed.globals _ _ found).1
    simpa only [Term.rename, renameArgs, closed_rename closed] using
      (HasType.global (ctx := Δ) (ghost := _) found)
  case ind =>
    rename_i family entry count fields sourceLoans ctx mode found arity size typedIndices ih Δ targetLoans ρ hρ
    have lifted := HasType.ind (ctx := Δ) (ghost := mode) (xs := fields.map (Term.rename ρ)) found arity
      (by simpa only [List.length_map] using size)
      (fun index member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        simpa only [Term.rename, renameArgs] using ih old oldMember Δ targetLoans ρ hρ)
    simpa only [Term.rename, renameArgs_ind, apply_ite, renameArgs] using lifted
  case con =>
    rename_i family entry constructor signature count sourceLoans ctx mode fields arity indices found signatureFound size arguments ih Δ targetLoans ρ hρ
    have signatureScope := wellFormed.signatures _ _ found signature (List.mem_of_getElem? signatureFound)
    have closed := signatureScope.signatureTerm_scoped family
    have lifted := ih Δ targetLoans ρ hρ
    have arguments' : Arguments env targetLoans Δ mode entry.declaration.data
        ((signatureTerm family signature).rename (fun x => x + Δ.length))
        (fields.map (Term.rename ρ)) (.node (.ind family arity) (indices.map (Term.rename ρ))) := by
      simpa only [closed_rename closed, Term.rename, renameArgs_ind] using lifted
    have result := HasType.con found signatureFound (by simpa only [List.length_map] using size) arguments'
    simpa only [Term.rename, renameArgs_con, renameArgs_ind] using result
  case propElim =>
    rename_i sourceMode found isProp motiveTyped casesTyped scrutineeTyped ihm ihc ihs Δ targetLoans ρ hρ
    have result := HasType.propElim (ghost := sourceMode) found isProp
      (by simpa only [propMotiveType_rename] using ihm Δ targetLoans ρ hρ)
      (ihc Δ targetLoans ρ hρ (wellFormed.signatures _ _ found))
      (by simpa only [Term.rename, renameArgs_ind] using ihs Δ targetLoans ρ hρ)
    simpa only [Term.rename, renameArgs_elim, List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      List.length_map, applications_rename] using result
  case buffer =>
    rename_i typed ih Δ targetLoans ρ hρ
    simpa only [rename_buffer, Term.rename, renameArgs] using HasType.buffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ targetLoans ρ hρ))
  case alloc =>
    rename_i count value ihc ihv Δ targetLoans ρ hρ
    simpa only [rename_alloc, rename_buffer, Term.rename, renameArgs] using HasType.alloc ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihc Δ targetLoans ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ targetLoans ρ hρ))
  case store =>
    rename_i buffer index value proof ihb ihi ihv ihp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.store ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ targetLoans ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ targetLoans ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ targetLoans ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ targetLoans ρ hρ))
  case load =>
    rename_i buffer index proof continuation value owner converted lowered allowed ihb ihi ihp ihk Δ targetLoans ρ hρ
    have hk := ihk Δ targetLoans ρ hρ
    have cv := value.renaming ρ wellFormed.closed
    have co := owner.renaming (Indexed.liftRenaming ρ) wellFormed.closed
    have cr := converted.renaming (liftRenaming 2 ρ) wellFormed.closed
    rw [load_result_rename ρ lowered] at cr
    have result := HasType.load (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ targetLoans ρ hρ)
      (by simpa [Term.rename, renameArgs] using ihi Δ targetLoans ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ targetLoans ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using hk)
      (by simpa [Term.rename, renameArgs] using cv)
      (by simpa only [rename_buffer, rename_shift_one] using co)
      cr (load_result_shifted _) (code_guard_rename allowed ρ wellFormed.closed)
    simpa only [rename_load] using result
  case free =>
    rename_i buffer rest ihb ihr Δ targetLoans ρ hρ
    simpa only [rename_free, rename_buffer] using HasType.free ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ targetLoans ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ targetLoans ρ hρ))
  case refBuffer =>
    rename_i count ih Δ targetLoans ρ hρ
    simpa only [rename_ref, rename_buffer, Term.rename, renameArgs] using HasType.refBuffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ targetLoans ρ hρ))
  case ghostBorrow =>
    rename_i buffer ih Δ targetLoans ρ hρ
    simpa only [rename_borrow, rename_ref, rename_buffer] using HasType.ghostBorrow ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ targetLoans ρ hρ))
  case ghostDeref =>
    rename_i reference ih Δ targetLoans ρ hρ
    simpa only [rename_deref, rename_ref, rename_buffer] using HasType.ghostDeref ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ targetLoans ρ hρ))
  case borrowedIndex =>
    rename_i reference index proof ihr ihi ihp Δ targetLoans ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.borrowedIndex ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ targetLoans ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ targetLoans ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ targetLoans ρ hρ))
  case nil =>
    rename_i converted Δ targetLoans ρ hρ
    simpa only [List.map_nil] using Arguments.nil (ctx := Δ) (ghost := _) (converted.renaming ρ wellFormed.closed)
  case cons =>
    rename_i telescope erased domain rest sourceLoans ctx mode data argument arguments result converted typed argumentsTyped iht iha Δ targetLoans ρ hρ
    have tail := iha Δ targetLoans ρ hρ
    change Arguments env targetLoans Δ mode data ((rest.subst (single argument)).rename ρ)
      (arguments.map (Term.rename ρ)) (result.rename ρ) at tail
    rw [Term.rename_instantiate] at tail
    have result := Arguments.cons (env := env) (ctx := Δ) (ghost := _) (data := data) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ wellFormed.closed)
      (by simpa using iht Δ targetLoans ρ hρ)
      tail
    simpa only [List.map_cons] using result
  case nil =>
    exact Cases.nil
  case cons =>
    rename_i typed branches iht ihb Δ targetLoans ρ hρ scopes
    have branch := iht Δ targetLoans ρ hρ
    rw [propCaseType_rename (scopes _ (by simp))] at branch
    exact Cases.cons branch (ihb Δ targetLoans ρ hρ (fun signature member => scopes signature (by simp [member])))
  case nil => exact BranchTypes.nil
  case cons =>
    rename_i typed branches iht ihb Δ targetLoans ρ hρ
    simpa only [List.map_cons] using BranchTypes.cons (iht Δ targetLoans ρ hρ) (ihb Δ targetLoans ρ hρ)

  case codeBorrowOwned =>
    rename_i source owned active ih Δ targetLoans ρ hρ
    simpa only [rename_borrow,rename_ref,Term.rename] using
      HasType.codeBorrowOwned (by simpa only [Term.rename] using ih Δ targetLoans ρ hρ)
        (owned.renaming ρ wellFormed.closed) (hρ.active _ active)
  case lendGeneric =>
    rename_i ownerTyped owned outlived readerTyped continuationTyped allowed iho ihr ihc Δ targetLoans ρ hρ
    have target := HasType.lendGeneric (ghost := _)
      (iho Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed) (outlived.renaming wellFormed.closed ρ)
      (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,rename_shift_one] using ihr Δ targetLoans ρ hρ)
      (by simpa only [Term.rename,renameArgs,Op.binders,liftRenaming,rename_shift_one] using ihc Δ targetLoans ρ hρ)
      (code_guard_rename allowed ρ wellFormed.closed)
    simpa only [Lending.rename_lend] using target
  case lendDependentCode =>
    rename_i ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted
      continuationTyped converted removed allowed iho ihd ihr ihc Δ targetLoans ρ hρ
    have reweakens := Checker.branch_type_reweakens removed
    have converted' := converted.renaming (Indexed.liftRenaming ρ) wellFormed.closed
    rw [← reweakens,rename_shift_one] at converted'
    have again' := againConverted.renaming (Indexed.liftRenaming ρ) wellFormed.closed
    rw [rename_shift_one] at again'
    have target := HasType.lendDependentCode
      (by simpa only [Term.rename] using iho Δ targetLoans ρ hρ) (owned.renaming ρ wellFormed.closed)
      (ihd Δ targetLoans ρ hρ)
      (by simpa only [rename_ref] using domainConverted.renaming ρ wellFormed.closed)
      (by simpa only [Lending.read_rename,Term.rename] using ihr Δ _ ρ (hρ.enter _))
      (outlived.renaming wellFormed.closed ρ) (firstConverted.renaming ρ wellFormed.closed) again'
      (by simpa only [Lending.restore_rename,Term.rename,renameArgs,Op.binders,liftRenaming] using
        ihc Δ targetLoans ρ hρ)
      converted' (shifted_one _) (code_guard_rename allowed ρ wellFormed.closed)
    simpa only [Lending.rename_lend,Term.lam,Term.rename,renameArgs,Op.binders,liftRenaming] using target
  case lendDependentGhost =>
    rename_i ownerTyped owned domainTyped domainConverted readerTyped outlived firstConverted againConverted
      continuationTyped converted removed iho ihd ihr ihc Δ targetLoans ρ hρ
    exact dependent_rename_target wellFormed ρ owned domainConverted outlived firstConverted againConverted
      converted removed (iho Δ targetLoans ρ hρ) (ihd Δ targetLoans ρ hρ) (ihr Δ targetLoans ρ hρ) (ihc Δ targetLoans ρ hρ)

/-- Capture-avoiding variable renaming preserves the original source mode and
all Loan64 typing rules under the supplied active-loan map. -/
theorem HasType.codeRenaming (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type)
    (renamed : CodeRenaming loans ctx targetLoans target indices) :
    HasType env targetLoans target mode (term.rename indices) (type.rename indices) :=
  code_renaming_rule wellFormed typed target targetLoans indices renamed

private def openVariable (selected : Nat) : Nat → Nat
  | 0 => selected
  | n + 1 => n

/-- Opening a binder with an existing variable preserves lookup annotations
and loan permissions when that variable has the binder's annotation and
erasure flag. Existing loans are already entered before the new binder. -/
theorem CodeRenaming.instantiateVariable
    (entered : Loans.Entered ctx.length loans)
    (selected : lookup ctx index = some ⟨domain, erased⟩) :
    CodeRenaming loans (⟨domain, erased⟩ :: ctx) loans ctx (openVariable index) := by
  have unshift (term : Term) : (term.rename Nat.succ).rename (openVariable index) = term := by
    rw [Term.rename_comp]
    exact term.rename_id
  refine ⟨?_, ?_, ?_⟩
  · intro source binding found
    cases source with
    | zero =>
        simp only [lookup, Option.some.injEq] at found
        subst binding
        simpa only [openVariable, unshift] using selected
    | succ source =>
        obtain ⟨previous, previousFound, rfl⟩ := Option.map_eq_some_iff.mp found
        simpa only [openVariable, unshift] using previousFound
  · intro frame member
    exact Nat.le_trans (entered frame member) (Nat.le_succ _)
  · intro owner allowed
    cases owner with
    | zero =>
        obtain ⟨frame, member, _, selected⟩ := Loans.active_iff.mp allowed
        have before := entered frame member
        simp only [List.length_cons] at selected
        omega
    | succ owner =>
        simpa only [List.length_cons, Loans.active_weaken entered, openVariable] using allowed

/-- Variable beta preserves the exact requested source type in the original
mode. Aliasing a binder to an existing variable preserves named borrowing
and every representation restriction guarded by the Loan64 derivation. -/
theorem HasType.codeVariableBeta {index : Nat}
    (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode (.app (.lam erased domain body) (.var index)) type)
    (entered : Loans.Entered ctx.length loans)
    (selected : lookup ctx index = some ⟨domain, erased⟩) :
    HasType env loans ctx mode (body.subst (single (.var index))) type := by
  obtain ⟨_, _, _, function, _, _, converted⟩ := typed.appView
  obtain ⟨_, _, _, bodyTyped, functionConverted⟩ := function.lamView
  obtain ⟨_, _, resultConverted⟩ := functionConverted.pi_injective wf.admissible
  have variableSub : single (.var index) = fun n => .var (openVariable index n) := by
    funext n
    cases n <;> rfl
  have reduced := bodyTyped.codeRenaming wf (CodeRenaming.instantiateVariable entered selected)
  have result := (resultConverted.substitution (single (.var index)) wf.closed).trans converted
  rw [variableSub, Environment.variable_subst_eq_rename] at result ⊢
  exact reduced.convert result

end Jihoo.NativeKernel.Environment.LoanTyping
