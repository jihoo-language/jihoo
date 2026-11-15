import Jihoo.NativeFamilyIotaParallelConfluence

/-! Actual finite forward realization of the enlarged quotient parallel
calculus; arithmetic residual endpoints are explicit, not assumed normal forms. -/
namespace Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
open NativeKernel.Conversion (ListRel)
open ACU

inductive Mixed (env : Environment) : Term → Term → Prop where
  | refl (term : Term) : Mixed env term term
  | arithmetic : ArithmeticRed a b → Mixed env a b
  | compute : Computes a b → Mixed env a b
  | iota : Root env a b → Mixed env a b
  | trans : Mixed env a b → Mixed env b c → Mixed env a c
  | node (op : Op) : NativeKernel.Conversion.ListRel (Mixed env) xs ys → Mixed env (.node op xs) (.node op ys)

variable {env : Environment}
local notation "QPar" => Parallel env
local notation "QAtom" => Atom env
local notation "QStar" => Star env
local notation "MixedRed" => Mixed env
set_option linter.unusedSimpArgs false

theorem Mixed.toForward (step : MixedRed a b) : Extended.Forward env a b := by
  induction step using Mixed.rec (motive_2 := fun xs ys _ => ListRel (Extended.Forward env) xs ys) with
  | refl => exact .refl
  | arithmetic original => exact .old (.acu (.arithmetic original))
  | compute original => exact .old (.acu (.compute original))
  | iota original => exact .iota original
  | trans _ _ first second => exact first.trans second
  | node op _ ih => exact .node op ih
  | nil => exact .nil
  | cons _ _ first rest => exact .cons first rest

private theorem reorder (p : xs.Perm zs) (h : ListRel R xs ys) :
    ∃ ws, ys.Perm ws ∧ ListRel R zs ws := by
  induction p generalizing ys with
  | nil => cases h; exact ⟨[],.nil,.nil⟩
  | cons x p ih => cases h with
    | cons hx hs =>
        obtain ⟨ws,hp,hr⟩ := ih hs
        exact ⟨_::ws,hp.cons _,.cons hx hr⟩
  | swap x y xs => cases h with | cons hx hs => cases hs with
    | cons hy hs => exact ⟨_,List.Perm.swap _ _ _,.cons hy (.cons hx hs)⟩
  | trans p q ip iq =>
      obtain ⟨ws,hp,hr⟩ := ip h
      obtain ⟨vs,hq,hs⟩ := iq hr
      exact ⟨vs,hp.trans hq,hs⟩

private theorem one (h : ListRel R [a] ys) : ∃ b, ys = [b] ∧ R a b := by
  cases h with | cons h hs => cases hs; exact ⟨_,rfl,h⟩
private theorem two (h : ListRel R [a,b] ys) : ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases h with | cons ha hs =>
    obtain ⟨b',rfl,hb⟩ := one hs
    exact ⟨_,_,rfl,ha,hb⟩
private theorem three (h : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',rfl,hb,hc⟩ := two hs
    exact ⟨_,_,_,rfl,ha,hb,hc⟩
private theorem four (h : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases h with | cons ha hs =>
    obtain ⟨b',c',d',rfl,hb,hc,hd⟩ := three hs
    exact ⟨_,_,_,_,rfl,ha,hb,hc,hd⟩

private theorem lookup {k : Nat} (h : ListRel R xs ys) (selected : xs[k]? = some v) :
    ∃ w, ys[k]? = some w ∧ R v w := by
  induction h generalizing k with
  | nil => simp at selected
  | cons ha hs ih => cases k with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at selected; subst v; exact ⟨_,rfl,ha⟩
    | succ k => exact ih selected

private theorem arithmetic_sum (h : ListRel Arithmetic xs ys) : Arithmetic (sumTerms xs) (sumTerms ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => exact h.addCong ih

private theorem sum_compact (xs : List Term) : Arithmetic (sumTerms xs) (compact xs) := by
  induction xs with
  | nil => exact .refl _
  | cons x xs ih => cases xs with
    | nil => exact .zero x
    | cons y xs => exact .addCong (.refl x) ih

private theorem arithmetic_list (h : ListRel ArithmeticRed xs ys) : ListRel Arithmetic xs ys := by
  induction h with
  | nil => exact .nil
  | cons h hs ih => exact .cons h.toArithmetic ih

theorem Mixed.compact_pointwise (h : ListRel MixedRed xs ys) : MixedRed (compact xs) (compact ys) := by
  induction h with
  | nil => exact .refl _
  | cons h hs ih => cases hs with
    | nil => exact h
    | cons hb hs => exact .node .uadd (.cons h (.cons ih .nil))

private theorem list_length (related : ListRel R xs ys) : xs.length = ys.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem list_append (first : ListRel R xs ys) (second : ListRel R rest rest') :
    ListRel R (xs ++ rest) (ys ++ rest') := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

private theorem split_family_append (related : ListRel R (xs ++ rest) ys) :
    ∃ frontTerms suffix,ys = frontTerms ++ suffix ∧ ListRel R xs frontTerms ∧ ListRel R rest suffix := by
  induction xs generalizing ys with
  | nil => exact ⟨[],ys,rfl,.nil,related⟩
  | cons x xs ih => cases related with
    | cons head tail =>
      obtain ⟨frontTerms,suffix,rfl,front,last⟩ := ih tail
      exact ⟨_::frontTerms,suffix,rfl,.cons head front,last⟩

private theorem family_layout (related : ListRel R (motive :: (cases ++ [scrutinee])) children) :
    ∃ motive' cases' scrutinee',children = motive' :: (cases' ++ [scrutinee']) ∧
      R motive motive' ∧ ListRel R cases cases' ∧ R scrutinee scrutinee' := by
  cases related with
  | cons head tail =>
    obtain ⟨frontTerms,suffix,rfl,front,last⟩ := split_family_append tail
    obtain ⟨scrutinee',rfl,scrut⟩ := one last
    exact ⟨_,frontTerms,scrutinee',rfl,head,front,scrut⟩

private theorem arithmetic_congruence : Extended.Congruence Arithmetic :=
  ⟨by intro op ordinary xs ys related;exact .node op related⟩

/-- Every quotient parallel computation has an actual forward realization up
to a proved arithmetic endpoint. The strengthened source quantifier handles
heads exposed by zero elimination, without inserting additive zeros anywhere. -/
theorem Parallel.realize (h : QPar a b) : ∀ {a'}, Arithmetic a a' →
    ∃ c, MixedRed a' c ∧ Arithmetic b c := by
  induction h using Parallel.rec
    (motive_2 := fun x y _ => ∀ {z}, ArithmeticAtom x z → ∃ c, MixedRed z c ∧ Arithmetic y c)
    (motive_3 := fun xs ys _ => ∀ {zs}, ListRel ArithmeticAtom xs zs →
      ∃ cs, ListRel MixedRed zs cs ∧ ListRel Arithmetic ys cs)
    (motive_4 := fun xs ys _ => ∀ {zs}, ListRel Arithmetic xs zs →
      ∃ cs, ListRel MixedRed zs cs ∧ ListRel Arithmetic ys cs) with
  | intro p hs out ih =>
      intro a' eqv
      obtain ⟨zs,hp,hr⟩ := eqv.model.matching ArithmeticAtom.refl ArithmeticAtom.symm ArithmeticAtom.trans
      obtain ⟨ws,wp,wr⟩ := reorder (hp.symm.trans p) hr
      obtain ⟨cs,hcs,ecs⟩ := ih wr
      exact ⟨compact cs,
        (Mixed.arithmetic (ArithmeticRed.flatten a')).trans
          ((Mixed.arithmetic (ArithmeticRed.compact_perm wp)).trans (Mixed.compact_pointwise hcs)),
        out.trans ((arithmetic_sum ecs).trans (sum_compact cs))⟩
  | var x => rename_i z eqv; cases eqv; exact ⟨_,.refl _,.refl _⟩
  | node op hs ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨cs,hcs,ecs⟩ := ih kids
          exact ⟨_,.node op hcs,.node op ecs⟩
  | beta e A body view hb ha ib ia =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨fT,aT,rfl,hf,haa⟩ := two kids
          obtain ⟨ls,forward,inner⟩ := ((hf.symm.trans view).symm).forward_node rfl
          obtain ⟨A0,body0,rfl,hA,hbody⟩ := two inner
          obtain ⟨bodyC,hbodyC,ebodyC⟩ := ib hbody.toArithmetic
          obtain ⟨aC,haC,eaC⟩ := ia haa
          have function : MixedRed fT (.lam e A0 bodyC) :=
            (Mixed.arithmetic forward).trans (.node (.lam e) (.cons (.refl A0) (.cons hbodyC .nil)))
          exact ⟨_,(Mixed.node .app (.cons function (.cons haC .nil))).trans (.compute (.beta e A0 bodyC aC)),
            ACU.Arithmetic.instantiate ebodyC eaC⟩
  | sub m n p left right bound valid =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,pT,rfl,ha,hb,hp⟩ := three kids
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(Mixed.node .usub (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl pT) .nil)))).trans
            (.compute (.sub m n pT bound valid)),.refl _⟩
  | read count k p arr index hs selected ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,iT,pT,rfl,ha,hi,hp⟩ := three kids
          obtain ⟨xs0,forward,inner⟩ := ((ha.symm.trans arr).symm).forward_node rfl
          obtain ⟨cs,hcs,ecs⟩ := ih (arithmetic_list inner)
          obtain ⟨c,selectedC,ec⟩ := lookup ecs selected
          have ra : MixedRed aT (.elements count cs) :=
            (Mixed.arithmetic forward).trans (.node (.elements count) hcs)
          have rk := ((hi.symm.trans index).symm).recover_natural
          exact ⟨c,(Mixed.node .index (.cons ra (.cons (.arithmetic rk) (.cons (.refl pT) .nil)))).trans
            (.compute (.read count cs k pT c selectedC)),ec⟩
  | witnessPack p a q view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨p0,a0,q0,rfl,hp,haa,hq⟩ := three inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((Mixed.node .witness (.cons (.arithmetic forward) .nil)).trans
            (.compute (.witnessPack p0 a0 q0))).trans hc,ec⟩
  | proofPack p a q view hq ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨p0,a0,q0,rfl,hp,ha,hqq⟩ := three inner
          obtain ⟨c,hc,ec⟩ := ih hqq.toArithmetic
          exact ⟨c,((Mixed.node .proof (.cons (.arithmetic forward) .nil)).trans
            (.compute (.proofPack p0 a0 q0))).trans hc,ec⟩
  | derefBorrow a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((Mixed.node .deref (.cons (.arithmetic forward) .nil)).trans
            (.compute (.derefBorrow a0))).trans hc,ec⟩
  | borrowDeref a view ha ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨tT,rfl,ht⟩ := one kids
          obtain ⟨xs0,forward,inner⟩ := ((ht.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih haa.toArithmetic
          exact ⟨c,((Mixed.node .borrow (.cons (.arithmetic forward) .nil)).trans
            (.compute (.borrowDeref a0))).trans hc,ec⟩
  | transportRefl a view hp ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨fT,rT,pT,rfl,hf,hr,hpp⟩ := three kids
          obtain ⟨xs0,forward,inner⟩ := ((hr.symm.trans view).symm).forward_node rfl
          obtain ⟨a0,rfl,haa⟩ := one inner
          obtain ⟨c,hc,ec⟩ := ih hpp
          exact ⟨c,((Mixed.node .transport (.cons (.refl fT) (.cons (.arithmetic forward) (.cons (.refl pT) .nil)))).trans
            (.compute (.transportRefl fT a0 pT))).trans hc,ec⟩
  | ifLtTrue m n no left right bound hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hyes
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(Mixed.node .ifLt (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons hc (.cons (.refl noT) .nil))))).trans
            (.compute (.ifLtTrue m n c noT bound)),ACU.Arithmetic.instantiate ec (.refl _)⟩
  | ifLtFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hno
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨c,(Mixed.node .ifLt (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl yesT) (.cons hc .nil))))).trans
            (.compute (.ifLtFalse m n yesT c bound)),ec⟩
  | ifEqTrue n no left right hy ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hyes
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨_,(Mixed.node .ifEq (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons hc (.cons (.refl noT) .nil))))).trans
            (.compute (.ifEqTrue n c noT)),ACU.Arithmetic.instantiate ec (.refl _)⟩
  | ifEqFalse m n yes left right bound hn ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨aT,bT,yesT,noT,rfl,ha,hb,hyes,hno⟩ := four kids
          obtain ⟨c,hc,ec⟩ := ih hno
          have ra := ((ha.symm.trans left).symm).recover_natural
          have rb := ((hb.symm.trans right).symm).recover_natural
          exact ⟨c,(Mixed.node .ifEq (.cons (.arithmetic ra) (.cons (.arithmetic rb) (.cons (.refl yesT) (.cons hc .nil))))).trans
            (.compute (.ifEqFalse m n yesT c bound)),ec⟩
  | elim family constructor entry signature motive cases scrutinee found sigFound count fields view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i values motiveOut casesOut valuesOut branchOut z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveT,casesT,scrutineeT,rfl,motiveChange,casesChange,scrutineeChange⟩ := family_layout kids
          obtain ⟨valuesT,expose,inside⟩ := ((scrutineeChange.symm.trans view).symm).forward_node (by rfl)
          obtain ⟨motiveC,motivePath,motiveEqual⟩ := ihMotive motiveChange
          obtain ⟨casesC,casePaths,casesEqual⟩ := ihCases casesChange
          obtain ⟨valuesC,valuePaths,valuesEqual⟩ := ihValues (arithmetic_list inside)
          obtain ⟨branchC,selectedC,rootC,outputEqual⟩ := elim_residual arithmetic_congruence found sigFound selected
            ((list_length caseSteps).symm.trans count) ((list_length valueSteps).symm.trans fields)
            motiveEqual casesEqual valuesEqual
          have valueCount := (list_length valueSteps).trans (list_length valuesEqual)
          have caseCount := (list_length caseSteps).trans (list_length casesEqual)
          have scrutineePath : MixedRed scrutineeT (.node (.con family constructor valuesC.length) valuesC) := by
            simpa only [valueCount] using (Mixed.arithmetic expose).trans (Mixed.node (.con family constructor values.length) valuePaths)
          have sourcePath : MixedRed (.node (.elim family cases.length) (motiveT :: (casesT ++ [scrutineeT])))
              (elimTerm family motiveC casesC (.node (.con family constructor valuesC.length) valuesC)) := by
            simpa only [elimTerm,caseCount] using Mixed.node (.elim family cases.length)
              (.cons motivePath (list_append casePaths (.cons scrutineePath .nil)))
          exact ⟨_,sourcePath.trans (.iota rootC),outputEqual⟩
  | caseOf family constructor entry signature motive cases scrutinee found data sigFound count fields view caseSteps valueSteps selected ihCases ihValues =>
      rename_i values casesOut valuesOut branchOut z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveT,casesT,scrutineeT,rfl,motiveChange,casesChange,scrutineeChange⟩ := family_layout kids
          obtain ⟨valuesT,expose,inside⟩ := ((scrutineeChange.symm.trans view).symm).forward_node (by rfl)
          obtain ⟨casesC,casePaths,casesEqual⟩ := ihCases casesChange
          obtain ⟨valuesC,valuePaths,valuesEqual⟩ := ihValues (arithmetic_list inside)
          obtain ⟨branchC,selectedC,rootC,outputEqual⟩ := case_residual (motive' := motiveT) arithmetic_congruence found data sigFound selected
            ((list_length caseSteps).symm.trans count) ((list_length valueSteps).symm.trans fields) casesEqual valuesEqual
          have valueCount := (list_length valueSteps).trans (list_length valuesEqual)
          have caseCount := (list_length caseSteps).trans (list_length casesEqual)
          have scrutineePath : MixedRed scrutineeT (.node (.con family constructor valuesC.length) valuesC) := by
            simpa only [valueCount] using (Mixed.arithmetic expose).trans (Mixed.node (.con family constructor values.length) valuePaths)
          have sourcePath : MixedRed (.node (.caseOf family cases.length) (motiveT :: (casesT ++ [scrutineeT])))
              (caseTerm family motiveT casesC (.node (.con family constructor valuesC.length) valuesC)) := by
            simpa only [caseTerm,caseCount] using Mixed.node (.caseOf family cases.length)
              (.cons (Mixed.refl motiveT) (list_append casePaths (.cons scrutineePath .nil)))
          exact ⟨_,sourcePath.trans (.iota rootC),outputEqual⟩
  | view recursion family constructor entry signature motive cases scrutinee found boxed sigFound count fields bound planned view motiveStep caseSteps valueSteps selected ihMotive ihCases ihValues =>
      rename_i plans values motiveOut casesOut valuesOut branchOut z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨motiveT,casesT,scrutineeT,rfl,motiveChange,casesChange,scrutineeChange⟩ := family_layout kids
          obtain ⟨borrowedT,expose,borrowInside⟩ := ((scrutineeChange.symm.trans view).symm).forward_node (by rfl)
          obtain ⟨constructorT,rfl,constructorInside⟩ := one borrowInside
          obtain ⟨valuesT,rfl,inside⟩ := constructorInside.rigid_shape (by rfl) rfl
          obtain ⟨motiveC,motivePath,motiveEqual⟩ := ihMotive motiveChange
          obtain ⟨casesC,casePaths,casesEqual⟩ := ihCases casesChange
          obtain ⟨valuesC,valuePaths,valuesEqual⟩ := ihValues (arithmetic_list inside)
          obtain ⟨branchC,selectedC,rootC,outputEqual⟩ := view_residual arithmetic_congruence found boxed sigFound selected
            ((list_length caseSteps).symm.trans count) ((list_length valueSteps).symm.trans fields) bound planned
            motiveEqual casesEqual valuesEqual
          have valueCount := (list_length valueSteps).trans (list_length valuesEqual)
          have caseCount := (list_length caseSteps).trans (list_length casesEqual)
          have scrutineePath : MixedRed scrutineeT (.borrow (.node (.con family constructor valuesC.length) valuesC)) := by
            simpa only [valueCount] using (Mixed.arithmetic expose).trans
              (Mixed.node .borrow (.cons (Mixed.node (.con family constructor values.length) valuePaths) .nil))
          have sourcePath : MixedRed (.node (.view recursion family cases.length) (motiveT :: (casesT ++ [scrutineeT])))
              (viewTerm recursion family motiveC casesC (.borrow (.node (.con family constructor valuesC.length) valuesC))) := by
            simpa only [viewTerm,caseCount] using Mixed.node (.view recursion family cases.length)
              (.cons motivePath (list_append casePaths (.cons scrutineePath .nil)))
          exact ⟨_,sourcePath.trans (.iota rootC),outputEqual⟩
  | drop family owner rest restStep ih =>
      rename_i z eqv
      cases eqv with
      | node _ kids =>
          obtain ⟨ownerT,restT,rfl,ownerChange,restChange⟩ := two kids
          obtain ⟨restC,restPath,restEqual⟩ := ih restChange
          exact ⟨restC,(Mixed.iota (.drop family ownerT restT)).trans restPath,restEqual⟩
  | nil => rename_i zs hs; cases hs; exact ⟨[],.nil,.nil⟩
  | cons h hs ih is =>
      rename_i zs kids
      cases kids with | cons k ks =>
        obtain ⟨c,hc,ec⟩ := ih k
        obtain ⟨cs,hcs,ecs⟩ := is ks
        exact ⟨c::cs,.cons hc hcs,.cons ec ecs⟩
  | _ =>
      first
        | rename_i zs kids; cases kids; exact ⟨[],.nil,.nil⟩
        | rename_i h hs ih is zs kids
          cases kids with | cons k ks =>
            obtain ⟨c,hc,ec⟩ := ih k
            obtain ⟨cs,hcs,ecs⟩ := is ks
            exact ⟨c::cs,.cons hc hcs,.cons ec ecs⟩

theorem Star.realize (h : QStar a b) : ∀ {a'}, Arithmetic a a' →
    ∃ c, MixedRed a' c ∧ Arithmetic b c := by
  induction h with
  | refl => intro a' eqv; exact ⟨a',.refl _,eqv⟩
  | cons h hs ih =>
      intro a' eqv
      obtain ⟨c,hc,ec⟩ := h.realize eqv
      obtain ⟨d,hd,ed⟩ := ih ec
      exact ⟨d,hc.trans hd,ed⟩


end Jihoo.NativeKernel.Environment.FamilyIota.Extended.Quotient
