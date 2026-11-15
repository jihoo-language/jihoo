import Jihoo.NativeFamilyIotaParallel

/-! Arithmetic input transport for the same enlarged quotient parallel relation. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU
variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env
set_option linter.unusedSimpArgs false

private theorem listRel_perm_left (p : xs.Perm zs) (h : ListRel R xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel R zs ws := by
  induction p generalizing ys with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | cons x p ih =>
      cases h with
      | cons hx hs =>
          obtain ⟨ws,hp,hr⟩ := ih hs
          exact ⟨_::ws,hp.cons _,.cons hx hr⟩
  | swap x y xs =>
      cases h with
      | cons hx hs => cases hs with
        | cons hy hs => exact ⟨_,List.Perm.swap _ _ _,.cons hy (.cons hx hs)⟩
  | trans p q ip iq =>
      obtain ⟨ws,hp,hr⟩ := ip h
      obtain ⟨vs,hq,hs⟩ := iq hr
      exact ⟨vs,hp.trans hq,hs⟩

private theorem listRel_append (h : ListRel R xs ys) (k : ListRel R us vs) :
    ListRel R (xs ++ us) (ys ++ vs) := by
  induction h with
  | nil => exact k
  | cons ha hs ih => exact .cons ha ih

private theorem listRel_length (h : ListRel R xs ys) : xs.length = ys.length := by
  induction h <;> simp_all

private theorem split_append (related : ListRel R (xs ++ rest) ys) :
    ∃ frontTerms suffix,ys = frontTerms ++ suffix ∧ ListRel R xs frontTerms ∧ ListRel R rest suffix := by
  induction xs generalizing ys with
  | nil => exact ⟨[],ys,rfl,.nil,related⟩
  | cons x xs ih => cases related with
    | cons head tail =>
      obtain ⟨frontTerms,suffix,rfl,front,last⟩ := ih tail
      exact ⟨_::frontTerms,suffix,rfl,.cons head front,last⟩

private theorem one (related : ListRel R [term] terms) :
    ∃ result,terms = [result] ∧ R term result := by
  cases related with
  | cons head tail => cases tail;exact ⟨_,rfl,head⟩

private theorem layout (related : ListRel R (motive :: (cases ++ [scrutinee])) children) :
    ∃ motive' cases' scrutinee',children = motive' :: (cases' ++ [scrutinee']) ∧
      R motive motive' ∧ ListRel R cases cases' ∧ R scrutinee scrutinee' := by
  cases related with
  | cons head tail =>
    obtain ⟨frontTerms,suffix,rfl,front,last⟩ := split_append tail
    obtain ⟨scrutinee',rfl,scrut⟩ := one last
    exact ⟨_,frontTerms,scrutinee',rfl,head,front,scrut⟩

private theorem listArithmetic_one (h : ListRel Arithmetic [a] ys) : ∃ b, ys = [b] ∧ Arithmetic a b := by
  cases h with | cons h hs => cases hs; exact ⟨_,rfl,h⟩

private theorem listArithmetic_two (h : ListRel Arithmetic [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ Arithmetic a a' ∧ Arithmetic b b' := by
  cases h with | cons ha hs =>
    obtain ⟨b',rfl,hb⟩ := listArithmetic_one hs
    exact ⟨_,_,rfl,ha,hb⟩

private theorem listArithmetic_three (h : ListRel Arithmetic [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ Arithmetic a a' ∧ Arithmetic b b' ∧ Arithmetic c c' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',rfl,hb,hc⟩ := listArithmetic_two hs
    exact ⟨_,_,_,rfl,ha,hb,hc⟩

private theorem listArithmetic_four (h : ListRel Arithmetic [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ Arithmetic a a' ∧ Arithmetic b b' ∧ Arithmetic c c' ∧ Arithmetic d d' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := listArithmetic_three hs
    exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

/-- Parallel computation is well defined for every arithmetic-equivalent
representative of its source, with exactly the same displayed output. -/
theorem Parallel.input (h : QPar a b) : ∀ {a'}, Arithmetic a a' → QPar a' b := by
  induction h using Parallel.rec
    (motive_2 := fun x y _ => ∀ {z}, ArithmeticAtom x z → QAtom z y)
    (motive_3 := fun xs ys _ => ∀ {zs}, ListRel ArithmeticAtom xs zs → ListRel QAtom zs ys)
    (motive_4 := fun xs ys _ => ∀ {zs}, ListRel Arithmetic xs zs → ListRel QPar zs ys) with
  | intro p hs out ih =>
      intro a' eqv
      obtain ⟨zs,hp,hr⟩ := eqv.model.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
      obtain ⟨ws,wp,wr⟩ := listRel_perm_left (hp.symm.trans p) hr
      exact .intro wp (ih wr) out
  | var x => rename_i z eqv; cases eqv; exact .var x
  | node op hs ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids => exact .node op (ih kids)
  | beta e A body view hb ha ihb iha =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨f',a',rfl,hf,haa⟩ := listArithmetic_two kids
          exact .beta e A body (hf.symm.trans view) hb (iha haa)
  | sub m n p left right bound valid =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',p',rfl,ha,hb,hp⟩ := listArithmetic_three kids
          exact .sub m n p' (ha.symm.trans left) (hb.symm.trans right) bound valid
  | read count k p arr index hs selected ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',i',p',rfl,ha,hi,hp⟩ := listArithmetic_three kids
          exact .read count k p' (ha.symm.trans arr) (hi.symm.trans index) hs selected
  | witnessPack p a q view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .witnessPack p a q (ht.symm.trans view) ha
  | proofPack p a q view hq ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .proofPack p a q (ht.symm.trans view) hq
  | derefBorrow a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .derefBorrow a (ht.symm.trans view) ha
  | borrowDeref a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨t',rfl,ht⟩ := listArithmetic_one kids
          exact .borrowDeref a (ht.symm.trans view) ha
  | transportRefl a view hp ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨f',r',p',rfl,hf,hr,hpp⟩ := listArithmetic_three kids
          exact .transportRefl a (hr.symm.trans view) (ih hpp)
  | ifLtTrue m n no left right bound hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifLtTrue m n no' (ha.symm.trans left) (hb.symm.trans right) bound (ih hyes)
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifLtFalse m n yes' (ha.symm.trans left) (hb.symm.trans right) bound (ih hno)
  | ifEqTrue n no left right hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifEqTrue n no' (ha.symm.trans left) (hb.symm.trans right) (ih hyes)
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨a',b',yes',no',rfl,ha,hb,hyes,hno⟩ := listArithmetic_four kids
          exact .ifEqFalse m n yes' (ha.symm.trans left) (hb.symm.trans right) bound (ih hno)
  | elim family constructor entry signature motive cases scrutinee found sigFound count fields view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveNew,casesNew,scrutineeNew,rfl,motiveChange,casesChange,scrutineeChange⟩ := layout kids
          have built := Atom.elim family constructor entry signature motiveNew casesNew scrutineeNew
            found sigFound ((listRel_length casesChange).symm.trans count) fields
            (scrutineeChange.symm.trans view) (ihMotive motiveChange) (ihCases casesChange) valueSteps selected
          simpa only [elimTerm,listRel_length casesChange] using built
  | caseOf family constructor entry signature motive cases scrutinee found data sigFound count fields view caseSteps valueSteps selected ihCases ihValues =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveNew,casesNew,scrutineeNew,rfl,motiveChange,casesChange,scrutineeChange⟩ := layout kids
          have built := Atom.caseOf family constructor entry signature motiveNew casesNew scrutineeNew
            found data sigFound ((listRel_length casesChange).symm.trans count) fields
            (scrutineeChange.symm.trans view) (ihCases casesChange) valueSteps selected
          simpa only [caseTerm,listRel_length casesChange] using built
  | view recursion family constructor entry signature motive cases scrutinee found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveNew,casesNew,scrutineeNew,rfl,motiveChange,casesChange,scrutineeChange⟩ := layout kids
          have built := Atom.view recursion family constructor entry signature motiveNew casesNew scrutineeNew
            found boxed sigFound ((listRel_length casesChange).symm.trans count) fields bound planned
            (scrutineeChange.symm.trans view) (ihMotive motiveChange) (ihCases casesChange) valueSteps selected
          simpa only [viewTerm,listRel_length casesChange] using built
  | drop family owner rest restStep ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨ownerNew,restNew,rfl,ownerChange,restChange⟩ := listArithmetic_two kids
          exact .drop family ownerNew restNew (ih restChange)
  | nil => rename_i zs hs; cases hs; exact .nil
  | cons h hs ih is => rename_i zs kids; cases kids with | cons k ks => exact .cons (ih k) (is ks)
  | _ =>
      rename_i zs kids
      cases kids
      all_goals first
        | exact .nil
        | rename_i k ks; exact .cons (by apply_assumption; exact k) (by apply_assumption; exact ks)


end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
