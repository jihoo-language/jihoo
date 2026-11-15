import Jihoo.NativeCodePolicyRenaming

/-! Mode-preserving capture-free renaming for every actual environment typing
rule, including code applications and all resource, data and view policies.
The map preserves actual lookup types and erased flags. Computations are not
substituted into runtime annotations. -/
namespace Jihoo.NativeKernel.Environment

set_option linter.unusedSimpArgs false

private theorem rename_shift_one (term : Term) (ρ : Nat → Nat) :
    (term.rename Nat.succ).rename (Indexed.liftRenaming ρ) = (term.rename ρ).rename Nat.succ := by
  rw [Term.rename_comp, Term.rename_comp]
  rfl

set_option linter.unusedSimpArgs false in
private theorem code_renaming_rule (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) :
    ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → HasType env Δ mode (term.rename ρ) (type.rename ρ) := by
  apply HasType.rec (t := typed)
    (motive_1 := fun ctx erased domain sort _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → Binder env Δ erased (domain.rename ρ) sort)
    (motive_2 := fun ctx mode term type _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ → HasType env Δ mode (term.rename ρ) (type.rename ρ))
    (motive_3 := fun ctx mode data telescope arguments result _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ →
      Arguments env Δ mode data (telescope.rename ρ) (arguments.map (Term.rename ρ)) (result.rename ρ))
    (motive_4 := fun ctx motive signatures branches _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ →
      (∀ signature ∈ signatures, UnifiedProgram.SignatureScoped signature) →
      Cases env Δ (motive.rename ρ) signatures (branches.map (Term.rename ρ)))
    (motive_5 := fun ctx mode types branches _ => ∀ Δ ρ, Ghost.Renaming ctx Δ ρ →
      BranchTypes env Δ mode (types.map (Term.rename ρ)) (branches.map (Term.rename ρ)))
  all_goals intros
  case intro =>
    rename_i typed allowed ih_typed Δ ρ hρ
    exact .intro (by simpa using ih_typed Δ ρ hρ) (binderAllowed_renaming wellFormed.closed allowed ρ)
  case var =>
    rename_i hx allowed Δ ρ hρ
    simpa only [Term.rename] using HasType.var (hρ _ _ hx) allowed
  case univ =>
    rename_i bound Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.univ (ctx := Δ) (ghost := _) bound)
  case prop =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.prop (ctx := Δ) (ghost := _))
  case u64 =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.u64 (ctx := Δ) (ghost := _))
  case i64 =>
    rename_i Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.i64 (ctx := Δ) (ghost := _))
  case natural =>
    rename_i bound Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.natural (ctx := Δ) (ghost := _) bound)
  case integer =>
    rename_i lo hi Δ ρ hρ
    simpa [Term.rename, renameArgs] using (HasType.integer (ctx := Δ) (ghost := _) lo hi)
  case array =>
    rename_i hn ih_hn Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.array (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hn Δ ρ hρ)
  case lt =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lt (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case eq =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.eq (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case pi =>
    rename_i hA hB ih_hA ih_hB Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pi (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (by simpa using ih_hB _ _ (hρ.lift _ _))
  case lam =>
    rename_i hA hb ih_hA ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.lam (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hA Δ ρ hρ) (ih_hb _ _ (hρ.lift _ _))
  case app =>
    rename_i ctx mode f e A B a hf ha allowed ih_hf ih_ha Δ ρ hρ
    change HasType env Δ mode ((Term.app f a).rename ρ) ((B.subst (single a)).rename ρ)
    rw [Term.rename_instantiate]
    simp only [Term.rename, renameArgs, Op.binders, liftRenaming]
    have hf' : HasType env Δ mode (f.rename ρ)
        (.pi e (A.rename ρ) (B.rename (Indexed.liftRenaming ρ))) := by
      simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ih_hf Δ ρ hρ
    have ha' : HasType env Δ (mode || e) (a.rename ρ) (A.rename ρ) := by
      simpa using ih_ha Δ ρ hρ
    exact HasType.app hf' ha' (allowed.renaming ρ wellFormed.closed)
  case uadd =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.uadd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case usub =>
    rename_i ha hb hp ih_ha ih_hb ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.usub (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case refl =>
    rename_i ha ih_ha Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.refl (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
  case zeroLe =>
    rename_i ha ih_ha Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.zeroLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
  case decide =>
    rename_i ha hb hab Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      (HasType.decide (ctx := Δ) (ghost := _) ha hb hab)
  case decideConverted =>
    rename_i ha hb ca cb hm hn hmn ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.decideConverted (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
        (by simpa [Term.rename, renameArgs] using ca.renaming ρ wellFormed.closed)
        (by simpa [Term.rename, renameArgs] using cb.renaming ρ wellFormed.closed) hm hn hmn
  case elements =>
    rename_i n xs Γ mode hn hb hs ih_hs Δ ρ hρ
    have ht := HasType.elements (ctx := Δ) (ghost := _)
      (xs := xs.map (Term.rename ρ)) (n := n) (by simpa using hn) (by simpa using hb)
      (fun y hy => by
        obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
        simpa [Term.rename,renameArgs] using ih_hs x hx Δ ρ hρ)
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ht
  case index =>
    rename_i ha hi hp ih_ha ih_hi ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.index (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hi Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case arith =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.arith (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case strict =>
    rename_i ha hb ih_ha ih_hb Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.strict (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ)
  case ltAdd =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltAdd (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case ltCancel =>
    rename_i ha hb hc hp ih_ha ih_hb ih_hc ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltCancel (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case ltLe =>
    rename_i ha hb hc hp hq ih_ha ih_hb ih_hc ih_hp ih_hq Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.ltLe (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hb Δ ρ hρ) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hc Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)
  case transport =>
    rename_i hf he hp ih_hf ih_he ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.transport
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hf Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_he Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case refine =>
    rename_i hp ih_hp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.refine (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
  case pack =>
    rename_i hp ha hq ih_hp ih_ha ih_hq Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.pack
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hp Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ha Δ ρ hρ)
        (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hq Δ ρ hρ)
  case witness =>
    rename_i hs ih_hs Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.witness (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)
  case proof =>
    rename_i hs ih_hs Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.proof (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_hs Δ ρ hρ)
  case ifLt =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifLt (by simpa [Term.rename,renameArgs] using iha Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ (hρ.lift _ true))
        (ihn Δ ρ hρ)
  case ifEq =>
    rename_i ha hb hy hn iha ihb ihy ihn Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using
      HasType.ifEq (by simpa [Term.rename,renameArgs] using iha Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihb Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming,Indexed.liftRenaming,Term.rename_comp] using ihy _ _ (hρ.lift _ true))
        (ihn Δ ρ hρ)
  case absurd =>
    rename_i hT hp allowed ihT ihp Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.absurd (by simpa using ihT Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihp Δ ρ hρ)
        (allowed.renaming ρ wellFormed.closed)
  case foldI64 =>
    rename_i hn hi hb allowed ihn ihi ihb Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.foldI64 (by simpa [Term.rename,renameArgs] using ihn Δ ρ hρ)
        (by simpa [Term.rename,renameArgs] using ihi Δ ρ hρ)
        (by simpa only [foldBodyType_rename] using ihb Δ ρ hρ) (allowed.renaming ρ)
  case loop =>
    rename_i hm motivePolicy hn hi hb bodyPolicy ihm ihn ihi ihb Δ ρ hρ
    simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using
      HasType.loop
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihm Δ ρ hρ)
        (motivePolicy.renaming ρ wellFormed.closed)
        (by simpa [Term.rename,renameArgs] using ihn Δ ρ hρ)
        (by simpa [Term.rename,renameArgs,Op.binders,liftRenaming] using ihi Δ ρ hρ)
        (by simpa only [loopBodyType_rename,Bool.true_or] using ihb Δ ρ hρ)
        (bodyPolicy.renaming ρ)
  case back =>
    rename_i formed owned motive allowed iho ihm Δ ρ hρ
    have target := HasType.back (ghost := _)
      (by simpa [Term.rename, renameArgs] using iho Δ ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ ρ hρ) (allowed.renaming ρ wellFormed.closed)
    simpa only [rename_back, Term.rename, renameArgs] using target
  case give =>
    rename_i owner owned motive allowed result iho ihm ihr Δ ρ hρ
    have target := HasType.give (ghost := _)
      (iho Δ ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihm Δ ρ hρ) (allowed.renaming ρ wellFormed.closed)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ)
    simpa only [rename_give, rename_back] using target
  case take =>
    rename_i value continuation owner result converted lowered allowed ihv ihk Δ ρ hρ
    have cv := owner.renaming ρ wellFormed.closed
    have cp := result.renaming (liftRenaming 1 ρ) wellFormed.closed
    rw [rename_takeResultType] at cp
    have cr := converted.renaming (liftRenaming 2 ρ) wellFormed.closed
    rw [load_result_rename ρ lowered] at cr
    have target := HasType.take (ghost := _)
      (by simpa only [rename_back] using ihv Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihk Δ ρ hρ)
      cv (by simpa only [rename_takeResultType, liftRenaming] using cp)
      cr (load_result_shifted _) (allowed.renaming ρ wellFormed.closed)
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using target
  case foldOwned =>
    rename_i count init owned body allowed ihc ihi ihb Δ ρ hρ
    have lifted := HasType.foldOwned (ghost := _)
      (by simpa [Term.rename, renameArgs] using ihc Δ ρ hρ) (ihi Δ ρ hρ) (owned.renaming ρ wellFormed.closed)
      (by simpa only [foldAccumulatorBodyType_rename] using ihb Δ ρ hρ) (allowed.renaming ρ)
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using lifted
  case dataElim =>
    rename_i family entry analysis ctx motive proof ghost scrutinee indices types caseTerms found isData boxed size motiveTyped scrutineeTyped generated branches allowed ihm ihs ihb Δ ρ hρ
    have hm := ihm Δ ρ hρ
    rw [dataMotiveType_rename] at hm
    have generated' := dataCaseTypes_rename_success (wellFormed.signatures _ _ found) generated Δ.length ρ
    have lifted := HasType.dataElim (ghost := _) (ctx := Δ) (analysis := analysis)
      (proof := proof) (indices := indices.map (Term.rename ρ)) found isData boxed
      (by simpa only [List.length_map] using size)
      (by simpa only [List.map_take] using hm)
      (by simpa only [Term.rename, renameArgs_ind, Bool.true_or] using ihs Δ ρ hρ)
      (by simpa only [List.map_take] using generated')
      (by simpa only [Bool.true_or] using ihb Δ ρ hρ)
      (by simpa only [Term.rename, renameArgs, Op.binders, liftRenaming, applications_rename, List.map_drop] using allowed.renaming ρ wellFormed.closed)
    cases analysis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Term.rename, apply_ite, renameArgs_elim, renameArgs_caseOf, List.map_cons, List.map_append,
      List.map_singleton, List.map_nil, List.length_map, applications_rename, List.map_drop,
      renameArgs, Op.binders, liftRenaming] using lifted
  case drop =>
    rename_i found boxed owner rest iho ihr Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.drop found boxed (by simpa [Term.rename, renameArgs_ind] using iho Δ ρ hρ) (ihr Δ ρ hρ)
  case refOwned =>
    rename_i owner owned ih Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using
      HasType.refOwned (by simpa [Term.rename, renameArgs] using ih Δ ρ hρ) (owned.renaming ρ wellFormed.closed)
  case ghostBorrowOwned =>
    rename_i owner owned ih Δ ρ hρ
    simpa only [rename_borrow, rename_ref] using HasType.ghostBorrowOwned (ih Δ ρ hρ) (owned.renaming ρ wellFormed.closed)
  case ghostDerefOwned =>
    rename_i reference ih Δ ρ hρ
    simpa only [rename_deref, rename_ref] using
      HasType.ghostDerefOwned (by simpa only [rename_ref] using ih Δ ρ hρ)
  case view =>
    rename_i family entry ctx ghost scrutinee indices motive dependent recursive types caseTerms found isData boxed arity size scrutineeTyped motiveTyped allowed generated branches ihs ihm ihb Δ ρ hρ
    have generated' := viewCaseTypes_rename_success (wellFormed.signatures _ _ found) generated Δ.length ρ
    have result := HasType.view (ctx := Δ) (ghost := _) (indices := indices.map (Term.rename ρ))
      (dependent := dependent) (recursion := recursive) found isData boxed arity
      (by simpa only [List.length_map] using size)
      (by simpa only [rename_ref,Term.rename,renameArgs_ind] using ihs Δ ρ hρ)
      (by simpa only [viewMotiveType_rename,Term.rename,renameArgs_ind] using ihm Δ ρ hρ)
      (allowed.renaming ρ wellFormed.closed) generated' (ihb Δ ρ hρ)
    simpa only [Term.rename,renameArgs_view,List.map_cons,List.map_append,List.map_singleton,List.map_nil,
      List.length_map,viewResult_rename] using result
  case convert =>
    rename_i ht hc ih_ht Δ ρ hρ
    exact .convert (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih_ht Δ ρ hρ) (hc.renaming ρ wellFormed.closed)
  case global =>
    rename_i found Δ ρ hρ
    have closed := (wellFormed.globals _ _ found).1
    simpa only [Term.rename, renameArgs, closed_rename closed] using
      (HasType.global (ctx := Δ) (ghost := _) found)
  case ind =>
    rename_i family entry count fields ctx mode found arity size typedIndices ih Δ ρ hρ
    have lifted := HasType.ind (ctx := Δ) (ghost := mode) (xs := fields.map (Term.rename ρ)) found arity
      (by simpa only [List.length_map] using size)
      (fun index member => by
        obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
        simpa only [Term.rename, renameArgs] using ih old oldMember Δ ρ hρ)
    simpa only [Term.rename, renameArgs_ind, apply_ite, renameArgs] using lifted
  case con =>
    rename_i family entry constructor signature count ctx mode fields arity indices found signatureFound size arguments ih Δ ρ hρ
    have signatureScope := wellFormed.signatures _ _ found signature (List.mem_of_getElem? signatureFound)
    have closed := signatureScope.signatureTerm_scoped family
    have lifted := ih Δ ρ hρ
    have arguments' : Arguments env Δ mode entry.declaration.data
        ((signatureTerm family signature).rename (fun x => x + Δ.length))
        (fields.map (Term.rename ρ)) (.node (.ind family arity) (indices.map (Term.rename ρ))) := by
      simpa only [closed_rename closed, Term.rename, renameArgs_ind] using lifted
    have result := HasType.con found signatureFound (by simpa only [List.length_map] using size) arguments'
    simpa only [Term.rename, renameArgs_con, renameArgs_ind] using result
  case propElim =>
    rename_i family entry ctx motive caseTerms scrutinee indices mode found isProp motiveTyped casesTyped scrutineeTyped ihm ihc ihs Δ ρ hρ
    have result := HasType.propElim (ghost := mode) found isProp
      (by simpa only [propMotiveType_rename] using ihm Δ ρ hρ)
      (ihc Δ ρ hρ (wellFormed.signatures _ _ found))
      (by simpa only [Term.rename, renameArgs_ind] using ihs Δ ρ hρ)
    simpa only [Term.rename, renameArgs_elim, List.map_cons, List.map_append, List.map_singleton, List.map_nil,
      List.length_map, applications_rename] using result
  case buffer =>
    rename_i typed ih Δ ρ hρ
    simpa only [rename_buffer, Term.rename, renameArgs] using HasType.buffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case alloc =>
    rename_i count value ihc ihv Δ ρ hρ
    simpa only [rename_alloc, rename_buffer, Term.rename, renameArgs] using HasType.alloc ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihc Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ ρ hρ))
  case store =>
    rename_i buffer index value proof ihb ihi ihv ihp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.store ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihv Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ))
  case load =>
    rename_i buffer index proof continuation value owner converted lowered allowed ihb ihi ihp ihk Δ ρ hρ
    have hk := ihk Δ ρ hρ
    have cv := value.renaming ρ wellFormed.closed
    have co := owner.renaming (Indexed.liftRenaming ρ) wellFormed.closed
    have cr := converted.renaming (liftRenaming 2 ρ) wellFormed.closed
    rw [load_result_rename ρ lowered] at cr
    have result := HasType.load (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ)
      (by simpa [Term.rename, renameArgs] using ihi Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ)
      (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using hk)
      (by simpa [Term.rename, renameArgs] using cv)
      (by simpa only [rename_buffer, rename_shift_one] using co)
      cr (load_result_shifted _) (allowed.renaming ρ wellFormed.closed)
    simpa only [rename_load] using result
  case free =>
    rename_i buffer rest ihb ihr Δ ρ hρ
    simpa only [rename_free, rename_buffer] using HasType.free ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihb Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ))
  case refBuffer =>
    rename_i count ih Δ ρ hρ
    simpa only [rename_ref, rename_buffer, Term.rename, renameArgs] using HasType.refBuffer ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case ghostBorrow =>
    rename_i buffer ih Δ ρ hρ
    simpa only [rename_borrow, rename_ref, rename_buffer] using HasType.ghostBorrow ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case ghostDeref =>
    rename_i reference ih Δ ρ hρ
    simpa only [rename_deref, rename_ref, rename_buffer] using HasType.ghostDeref ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ih Δ ρ hρ))
  case borrowedIndex =>
    rename_i reference index proof ihr ihi ihp Δ ρ hρ
    simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using HasType.borrowedIndex ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihr Δ ρ hρ))
      ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihi Δ ρ hρ)) ((by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using ihp Δ ρ hρ))
  case nil =>
    rename_i converted Δ ρ hρ
    simpa only [List.map_nil] using Arguments.nil (ctx := Δ) (ghost := _) (converted.renaming ρ wellFormed.closed)
  case cons =>
    rename_i telescope erased domain rest ctx mode data argument arguments result converted typed argumentsTyped iht iha Δ ρ hρ
    have tail := iha Δ ρ hρ
    change Arguments env Δ mode data ((rest.subst (single argument)).rename ρ)
      (arguments.map (Term.rename ρ)) (result.rename ρ) at tail
    rw [Term.rename_instantiate] at tail
    have result := Arguments.cons (env := env) (ctx := Δ) (ghost := _) (data := data) (by simpa [Term.rename, renameArgs, Op.binders, liftRenaming] using converted.renaming ρ wellFormed.closed)
      (by simpa only [Bool.true_or] using iht Δ ρ hρ)
      tail
    simpa only [List.map_cons] using result
  case nil =>
    exact Cases.nil
  case cons =>
    rename_i typed branches iht ihb Δ ρ hρ scopes
    have branch := iht Δ ρ hρ
    rw [propCaseType_rename (scopes _ (by simp))] at branch
    exact Cases.cons branch (ihb Δ ρ hρ (fun signature member => scopes signature (by simp [member])))
  case nil => exact BranchTypes.nil
  case cons =>
    rename_i typed branches iht ihb Δ ρ hρ
    simpa only [List.map_cons] using BranchTypes.cons (iht Δ ρ hρ) (ihb Δ ρ hρ)

/-- All sixty native typing constructors retain their original mode. The
only context premise is the existing exact lookup renaming relation. -/
theorem HasType.modeRenaming (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) {Δ : Context} {ρ : Nat → Nat}
    (renamed : Ghost.Renaming ctx Δ ρ) :
    HasType env Δ mode (term.rename ρ) (type.rename ρ) :=
  code_renaming_rule wellFormed typed Δ ρ renamed

/-- A runtime expression may be retained beneath a new binding while keeping
its code derivation. The inserted binding can have either erasure flag. -/
theorem HasType.modeWeaken (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) (domain : Term) (erased : Bool) :
    HasType env (⟨domain, erased⟩ :: ctx) mode
      (term.rename Nat.succ) (type.rename Nat.succ) :=
  typed.modeRenaming wellFormed (NativeKernel.Ghost.Renaming.shift ctx domain erased)

/-- Variable-only simultaneous substitution is the same capture-free
renaming, so runtime policies and the original mode are retained. -/
theorem HasType.variableSubstitution (wellFormed : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env ctx mode term type) {Δ : Context} {ρ : Nat → Nat}
    (renamed : Ghost.Renaming ctx Δ ρ) :
    HasType env Δ mode (term.subst (fun x => .var (ρ x)))
      (type.subst (fun x => .var (ρ x))) := by
  simpa only [variable_subst_eq_rename] using typed.modeRenaming wellFormed renamed


end Jihoo.NativeKernel.Environment
