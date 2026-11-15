import Jihoo.NativeLoanUniquenessAlgebra

/-! Local functionality for the complete loan judgment. The hereditary source
induction will supply direct-child functionality and the explicit Lend finish
functionality, rather than assuming typed callbacks at arbitrary inputs. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

def directChildren : Term → List Term
  | .var _ => []
  | .node _ children => children

def ChildrenUnique (env : Environment) (term : Term) : Prop :=
  ∀ child ∈ directChildren term,Unique env child

def FinishUnique (env : Environment) (term : Term) : Prop :=
  ∀ {loans ctx mode type},HasType env loans ctx mode term type → ∀ owner domain readerBody first again body,
    term = .lend owner (.lam false domain readerBody) (.lam false first (.lam false again body)) →
      Unique env (Lending.finish owner body (Lending.read owner readerBody))

private theorem explicit_lend_unique (wf : UnifiedProgram.EnvWellFormed env)
    (finish : FinishUnique env term)
    (left : HasType env loans ctx mode term first) (right : HasType env loans' ctx mode' term second)
    (same : term = .lend owner (.lam false domain readerBody) (.lam false firstDomain (.lam false again body))) :
    Conv env first second :=
  finish left owner domain readerBody firstDomain again body same
    (left.explicitLendFinish wf owner domain readerBody firstDomain again body same)
    (right.explicitLendFinish wf owner domain readerBody firstDomain again body same)

/-- Local functionality uses only smaller source inputs. Its finish premise is
discharged by the hereditary substitution induction, not an output-typing oracle. -/
theorem unique_of_inputs (wf : UnifiedProgram.EnvWellFormed env)
    (children : ChildrenUnique env term) (finish : FinishUnique env term)
    (ht : HasType env loans Γ mode term A) (hu : HasType env loans' Γ mode' term B) : Conv env A B := by
  have ih : ∀ child,child ∈ directChildren term → ∀ Γ mode mode' A B,
      ∀ {loans loans'},HasType env loans Γ mode child A → HasType env loans' Γ mode' child B → Conv env A B := by
    intro child member Γ mode mode' A B loans loans' left right
    exact children child member left right
  have hv := ht.principalView
  have hw := hu.principalView
  fun_cases PrincipalView env loans Γ mode term A <;> simp only [PrincipalView] at hv hw
  all_goals first | exact False.elim hv | exact .trans (.symm hv) hw | skip
  case case1 =>
    obtain ⟨b, hb, hc⟩ := hv
    obtain ⟨b', hb', hd⟩ := hw
    have same : b = b' := Option.some.inj (hb.symm.trans hb')
    subst b'
    exact .trans (.symm hc) hd
  case case25 =>
    rename_i e X Y
    obtain ⟨s,r,hX,hY,hc⟩ := hv
    obtain ⟨s',r',hX',hY',hd⟩ := hw
    have ds := ih X (by simp [directChildren]) Γ true true _ _ hX hX'
    have dr := ih Y (by simp [directChildren]) (⟨X,e⟩ :: Γ) true true _ _ hY hY'
    have ss := ds.sort_injective wf.admissible
    have rr := dr.sort_injective wf.admissible
    subst s'; subst r'
    exact .trans (.symm hc) hd
  case case26 =>
    rename_i e X body
    obtain ⟨Y,hY,hc⟩ := hv
    obtain ⟨Z,hZ,hd⟩ := hw
    have bodies := ih body (by simp [directChildren]) (⟨X,e⟩ :: Γ) mode mode' Y Z hY hZ
    exact .trans (.symm hc)
      (.trans (.node (.pi e) (.cons (.refl X) (.cons bodies .nil))) hd)
  case case27 =>
    rename_i f a
    obtain ⟨e,X,Y,hf,hc⟩ := hv
    obtain ⟨e',X',Y',hf',hd⟩ := hw
    have functions := ih f (by simp [directChildren]) Γ mode mode' _ _ hf hf'
    exact .trans (.symm hc) (.trans
      ((functions.pi_injective wf.admissible).2.2.substitution (single a) wf.closed) hd)
  case case28 =>
    rename_i a b
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have bodies := ih b (by simp [directChildren]) Γ mode mode' X Y hX hY
    exact .trans (.symm hc) (.trans bodies hd)
  case case29 =>
    rename_i f evidence p
    obtain ⟨a,b,he,hc⟩ := hv
    obtain ⟨a',b',he',hd⟩ := hw
    have equality := ih evidence (by simp [directChildren]) Γ true true _ _ he he'
    exact .trans (.symm hc)
      (.trans (.node .app (.cons (.refl f) (.cons (equality.eq_injective wf.admissible).2 .nil))) hd)
  case case30 =>
    rename_i s
    obtain ⟨p,hp,hc⟩ := hv
    obtain ⟨q,hq,hd⟩ := hw
    have predicates := ih s (by simp [directChildren]) Γ true true _ _ hp hq
    exact .trans (.symm hc)
      (.trans (.node .app (.cons (predicates.refine_injective wf.admissible) (.cons (.refl _) .nil))) hd)
  case case31 =>
    rename_i a b yes no
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have branches := ih no (by simp [directChildren]) Γ mode mode' X Y hX hY
    exact .trans (.symm hc) (.trans branches hd)
  case case32 =>
    rename_i a b yes no
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have branches := ih no (by simp [directChildren]) Γ mode mode' X Y hX hY
    exact .trans (.symm hc) (.trans branches hd)
  case case34 =>
    rename_i n init body
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    exact .trans (.symm hc) (.trans (ih init (by simp [directChildren]) Γ mode mode' X Y hX hY) hd)
  case case36 =>
    obtain ⟨declaration,found,hc⟩ := hv
    obtain ⟨declaration',found',hd⟩ := hw
    have same := Option.some.inj (found.symm.trans found')
    subst declaration'
    exact .trans (.symm hc) hd
  case case37 =>
    obtain ⟨entry,found,hc⟩ := hv
    obtain ⟨entry',found',hd⟩ := hw
    have same := Option.some.inj (found.symm.trans found')
    subst entry'
    exact .trans (.symm hc) hd
  case case38 =>
    obtain ⟨entry,signature,arity,indices,found,sigFound,args,hc⟩ := hv
    obtain ⟨entry',signature',arity',indices',found',sigFound',args',hd⟩ := hw
    have same := Option.some.inj (found.symm.trans found')
    subst entry'
    have same := Option.some.inj (sigFound.symm.trans sigFound')
    subst signature'
    exact .trans (.symm hc) (.trans (args.result_unique wf _ _ _ _ _ _ args' (.refl _)) hd)
  case case39 =>
    rename_i f count fields
    obtain ⟨entry,motive,branches,scrutinee,indices,scrutineeMode,found,countEq,layout,scrut,hc⟩ := hv
    obtain ⟨entry',motive',branches',scrutinee',indices',scrutineeMode',found',countEq',layout',scrut',hd⟩ := hw
    have entries := Option.some.inj (found.symm.trans found')
    subst entry'
    have layouts := List.cons.inj (layout.symm.trans layout')
    have motives := layouts.1
    subst motive'
    have ends := List.append_inj_right layouts.2 (countEq.symm.trans countEq')
    have scruts := (List.cons.inj ends).1
    subst scrutinee'
    have smaller : sizeOf scrutinee < sizeOf (Term.node (.elim f count) fields) := by
      have member : scrutinee ∈ fields := by rw [layout]; simp
      have bound := List.sizeOf_lt_of_mem member
      simp only [Term.node.sizeOf_spec]
      omega
    have indicesConv := ind_injective wf (ih scrutinee (by simp only [directChildren]; rw [layout]; simp) Γ scrutineeMode scrutineeMode' _ _ scrut scrut')
    exact .trans (.symm hc) (.trans (eliminationResult_congr _ _ _ indicesConv.2.2) hd)
  case case44 =>
    rename_i buffer index value proof
    obtain ⟨n,hn,hc⟩ := hv
    obtain ⟨m,hm,hd⟩ := hw
    have lengths := buffer_injective wf (ih buffer (by simp [directChildren]) Γ mode mode' _ _ hn hm)
    exact .trans (.symm hc) (.trans (.node .buffer (.cons lengths .nil)) hd)
  case case45 =>
    rename_i buffer rest
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    exact .trans (.symm hc) (.trans (ih rest (by simp [directChildren]) Γ mode mode' X Y hX hY) hd)
  case case46 =>
    rename_i buffer
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have owners := ih buffer (by simp [directChildren]) Γ true true X Y hX hY
    exact .trans (.symm hc) (.trans (.node .ref (.cons owners .nil)) hd)
  case case47 =>
    rename_i reference
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have owners := ref_injective wf (ih reference (by simp [directChildren]) Γ true true _ _ hX hY)
    exact .trans (.symm hc) (.trans owners hd)
  case case48 =>
    rename_i erased motive owner result
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    have owners := ih owner (by simp [directChildren]) Γ mode mode' X Y hX hY
    exact .trans (.symm hc) (.trans (.node (.back erased) (.cons owners (.cons (.refl _) .nil))) hd)
  case case49 =>
    rename_i buffer index proof continuation
    obtain ⟨X,e,Y,C,normal,outside,hκ,cn,lowered,hc⟩ := hv
    obtain ⟨X',e',Y',C',normal',outside',hκ',cn',lowered',hd⟩ := hw
    have first := (ih continuation (by simp [directChildren]) Γ mode mode' _ _ hκ hκ').pi_injective wf.admissible
    have results := (first.2.2.pi_injective wf.admissible).2.2
    have outsideConv := lowered_conversion wf lowered lowered' (.trans (.symm cn) (.trans results cn'))
    exact .trans (.symm hc) (.trans outsideConv hd)
  case case50 =>
    rename_i value continuation
    obtain ⟨X,e,Y,C,normal,outside,hκ,cn,lowered,hc⟩ := hv
    obtain ⟨X',e',Y',C',normal',outside',hκ',cn',lowered',hd⟩ := hw
    have first := (ih continuation (by simp [directChildren]) Γ mode mode' _ _ hκ hκ').pi_injective wf.admissible
    have results := (first.2.2.pi_injective wf.admissible).2.2
    have outsideConv := lowered_conversion wf lowered lowered' (.trans (.symm cn) (.trans results cn'))
    exact .trans (.symm hc) (.trans outsideConv hd)
  case case51 =>
    rename_i f count fields
    obtain ⟨entry,motive,branches,scrutinee,indices,scrutineeMode,found,countEq,layout,scrut,hc⟩ := hv
    obtain ⟨entry',motive',branches',scrutinee',indices',scrutineeMode',found',countEq',layout',scrut',hd⟩ := hw
    have entries := Option.some.inj (found.symm.trans found')
    subst entry'
    have layouts := List.cons.inj (layout.symm.trans layout')
    have motives := layouts.1
    subst motive'
    have ends := List.append_inj_right layouts.2 (countEq.symm.trans countEq')
    have scruts := (List.cons.inj ends).1
    subst scrutinee'
    have smaller : sizeOf scrutinee < sizeOf (Term.node (.elim f count) fields) := by
      have member : scrutinee ∈ fields := by rw [layout]; simp
      have bound := List.sizeOf_lt_of_mem member
      simp only [Term.node.sizeOf_spec]
      omega
    have indicesConv := ind_injective wf (ih scrutinee (by simp only [directChildren]; rw [layout]; simp) Γ scrutineeMode scrutineeMode' _ _ scrut scrut')
    exact .trans (.symm hc) (.trans (eliminationResult_congr _ _ _ indicesConv.2.2) hd)
  case case52 =>
    rename_i family owner rest
    obtain ⟨X,hX,hc⟩ := hv
    obtain ⟨Y,hY,hd⟩ := hw
    exact .trans (.symm hc) (.trans (ih rest (by simp [directChildren]) Γ mode mode' X Y hX hY) hd)
  case case53 =>
    rename_i recursion family count fields
    obtain ⟨entry,motive,branches,scrutinee,indices,scrutineeMode,dependent,found,countEq,layout,scrut,motiveTyped,hc⟩ := hv
    obtain ⟨entry',motive',branches',scrutinee',indices',scrutineeMode',dependent',found',countEq',layout',scrut',motiveTyped',hd⟩ := hw
    have layouts := List.cons.inj (layout.symm.trans layout')
    have motives := layouts.1
    subst motive'
    have ends := List.append_inj_right layouts.2 (countEq.symm.trans countEq')
    have scruts := (List.cons.inj ends).1
    subst scrutinee'
    have smaller : sizeOf motive < sizeOf (Term.node (.view recursion family count) fields) := by
      have member : motive ∈ fields := by rw [layout]; simp
      have bound := List.sizeOf_lt_of_mem member
      simp only [Term.node.sizeOf_spec]
      omega
    have dependencies := viewMotiveType_dependency_unique wf
      (ih motive (by simp only [directChildren]; rw [layout]; simp) Γ true true _ _ motiveTyped motiveTyped')
    subst dependent'
    exact .trans (.symm hc) hd
  case case54 =>
    rename_i owner reader continuation
    obtain ⟨principal,origin,converted⟩ := hv
    obtain ⟨principal',origin',converted'⟩ := hw
    cases origin with
    | generic ownerTyped owned outlived readerTyped continuationTyped allowed =>
        cases origin' with
        | generic ownerTyped' owned' outlived' readerTyped' continuationTyped' allowed' =>
            have functions := ih continuation (by simp [directChildren]) Γ mode mode' _ _ continuationTyped continuationTyped'
            have firstBody := (functions.pi_injective wf.admissible).2.2
            have unshifted := firstBody.substitution (single (.natural 0)) wf.closed
            simp only [Term.shift_subst_single] at unshifted
            have secondBody := (unshifted.pi_injective wf.admissible).2.2
            have results := secondBody.substitution (single (.natural 0)) wf.closed
            simp only [Term.shift_subst_single] at results
            exact converted.symm.trans (results.trans converted')
        | dependentCode => exact explicit_lend_unique wf finish ht hu rfl
        | dependentGhost => exact explicit_lend_unique wf finish ht hu rfl
    | dependentCode => exact explicit_lend_unique wf finish ht hu rfl
    | dependentGhost => exact explicit_lend_unique wf finish ht hu rfl

end Jihoo.NativeKernel.Environment.LoanTyping
