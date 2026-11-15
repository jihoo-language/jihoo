import Jihoo.NativeLoanContextConversion
import Jihoo.NativeLoanViewMotiveCongruence
import Jihoo.NativeLoanPrincipalInversion
import Jihoo.NativeLoanMemoryInversion
import Jihoo.NativeLoanAtomicEvaluation

/-! Typed closure below ordinary source nodes. Lend callbacks are specialized
and therefore its node is deliberately handled only by atomic root rules. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion
set_option linter.unusedSimpArgs false

theorem foldAccumulatorBodyType_congr (closed : Conversion.Closed env)
    (count : Conversion.Conv env n m) (accumulator : Conversion.Conv env A B) :
    Conversion.Conv env (foldAccumulatorBodyType n A) (foldAccumulatorBodyType m B) := by
  have proofType : Conversion.Conv env (.lt (.var 0) (n.rename Nat.succ)) (.lt (.var 0) (m.rename Nat.succ)) :=
    .node .lt (.cons (.refl _) (.cons (count.renaming Nat.succ closed) .nil))
  have stepType : Conversion.Conv env
      (.pi false (A.rename (fun x => x + 2)) (A.rename (fun x => x + 3)))
      (.pi false (B.rename (fun x => x + 2)) (B.rename (fun x => x + 3))) :=
    .node (.pi false) (.cons (accumulator.renaming (fun x => x + 2) closed)
      (.cons (accumulator.renaming (fun x => x + 3) closed) .nil))
  exact .node (.pi false) (.cons (.refl _) (.cons
    (.node (.pi true) (.cons proofType (.cons stepType .nil))) .nil))


theorem foldAccumulatorBodyType_count_congr (closed : Conversion.Closed env) (converted : Conversion.Conv env n m) :
    Conversion.Conv env (foldAccumulatorBodyType n accumulator) (foldAccumulatorBodyType m accumulator) :=
  foldAccumulatorBodyType_congr closed converted (.refl _)

theorem foldAccumulatorBodyType_accumulator_congr (closed : Conversion.Closed env) (converted : Conversion.Conv env A B) :
    Conversion.Conv env (foldAccumulatorBodyType count A) (foldAccumulatorBodyType count B) :=
  foldAccumulatorBodyType_congr closed (.refl _) converted

/-- Preserve every existing leading lambda, including its binder flag and an
actual conversion between annotations. New lambdas may be exposed at leaves. -/
def LambdaShape (env : Environment) : Term → Term → Prop
  | .lam erased domain body, output =>
      ∃ domain' body', output = .lam erased domain' body' ∧
        (Conv env) domain domain' ∧ LambdaShape env body body'
  | _, _ => True
termination_by input _ => sizeOf input

theorem LambdaShape.refl (term : Term) : LambdaShape env term term := by
  fun_cases LambdaShape env term term
  · rename_i erased domain body
    exact ⟨domain,body,rfl,.refl _,LambdaShape.refl body⟩
  · trivial
termination_by sizeOf term

theorem LambdaShape.trans (first : LambdaShape env a b) (second : LambdaShape env b c) : LambdaShape env a c := by
  fun_cases LambdaShape env a b <;> simp only [LambdaShape] at first ⊢
  · rename_i erased domain body
    obtain ⟨domain',body',rfl,domains,bodies⟩ := first
    simp only [LambdaShape] at second
    obtain ⟨domain'',body'',rfl,domains',bodies'⟩ := second
    exact ⟨domain'',body'',rfl,.trans domains domains',bodies.trans bodies'⟩
termination_by sizeOf a

structure GhostTransform (env : Environment) (input output : Term) : Prop where
  forward : RawLend.Forward env input output
  shape : LambdaShape env input output
  preserves : ∀ {ctx type}, HasType env [] ctx true input type → HasType env [] ctx true output type

theorem GhostTransform.refl (term : Term) : GhostTransform env term term :=
  ⟨.refl,LambdaShape.refl term,fun typed => typed⟩

theorem GhostTransform.trans (first : GhostTransform env a b) (second : GhostTransform env b c) :
    GhostTransform env a c :=
  ⟨.trans first.forward second.forward,first.shape.trans second.shape,
    fun typed => second.preserves (first.preserves typed)⟩

theorem GhostTransform.converted (change : GhostTransform env input output) : (Conv env) input output :=
  change.forward.toConv

theorem GhostTransform.typed (change : GhostTransform env a b) (typed : HasType env loans ctx mode a T) :
    HasType env [] ctx true b T := change.preserves (typed.ghost [])

theorem Arguments.convertTelescope (args : Arguments env loans ctx mode data telescope xs result)
    (converted : (Conv env) telescope' telescope) : Arguments env loans ctx mode data telescope' xs result := by
  cases args with
  | nil tail => exact .nil (.trans converted tail)
  | cons head typed tail => exact .cons (.trans converted head) typed tail

private theorem arguments_transport (closed : Conversion.Closed env) (args : Arguments env loans ctx mode data telescope xs result) :
    ∀ ys, ListRel (GhostTransform env) xs ys → Arguments env [] ctx true data telescope ys result := by
  apply Arguments.rec (t := args)
    (motive_1 := fun _ _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ ctx _ data telescope xs result _ =>
      ∀ ys, ListRel (GhostTransform env) xs ys → Arguments env [] ctx true data telescope ys result)
    (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i telescope result stack ctx mode data converted ys changes
    cases changes
    exact .nil converted
  case cons =>
    rename_i telescope erased domain rest stack ctx mode data argument arguments result converted typed tail _ ihtail ys changes
    cases changes with
    | cons headChange tailChanges =>
      rename_i newArgument newArguments
      have tailTyped := ihtail _ tailChanges
      have replacement : (Conv env) (rest.subst (single newArgument)) (rest.subst (single argument)) := by
        apply RawLend.Conv.subst_congr closed
        intro index
        cases index with
        | zero => exact .symm headChange.converted
        | succ index => exact .refl _
      apply Arguments.cons converted
      · simpa only [Bool.true_or] using headChange.typed typed
      · exact tailTyped.convertTelescope replacement

private theorem binary_congr (op : Op) (left : (Conv env) a a') (right : (Conv env) b b') :
    (Conv env) (.node op [a,b]) (.node op [a',b']) := .node op (.cons left (.cons right .nil))

private theorem hypothesisTelescope_congr (closed : Conversion.Closed env) (converted : (Conv env) a b) (bodies : (Conv env) body body') :
    (Conv env) (hypothesisTelescope fields offset recursive a body)
      (hypothesisTelescope fields offset recursive b body') := by
  induction recursive generalizing offset with
  | nil => exact bodies
  | cons pair rest ih =>
    simp only [hypothesisTelescope, List.zipIdx_cons, List.foldr_cons]
    exact binary_congr (.pi true)
      (applications_motive_congr (converted.renaming _ closed) _) (ih (offset := offset + 1))

private theorem fieldTelescope_congr (bodies : (Conv env) body body') (fields : List Field) :
    (Conv env) (fields.foldr (fun field rest => Term.pi field.erased field.domain rest) body)
      (fields.foldr (fun field rest => Term.pi field.erased field.domain rest) body') := by
  induction fields with
  | nil => exact bodies
  | cons field fields ih => exact binary_congr (.pi field.erased) (.refl _) ih

theorem propCaseType_congr (closed : Conversion.Closed env) (signature : Signature) (converted : (Conv env) a b) :
    (Conv env) (propCaseType signature a) (propCaseType signature b) := by
  rw [propCaseType_eq,propCaseType_eq]
  exact fieldTelescope_congr
    (hypothesisTelescope_congr closed converted (applications_motive_congr (converted.renaming _ closed) _)) _

theorem foldBodyType_congr (closed : Conversion.Closed env) (converted : (Conv env) n n') : (Conv env) (foldBodyType n) (foldBodyType n') := by
  unfold foldBodyType
  exact binary_congr (.pi false) (.refl _)
    (binary_congr (.pi true) (binary_congr .lt (.refl _) (converted.renaming Nat.succ closed)) (.refl _))

theorem loopBodyType_count_congr (closed : Conversion.Closed env) (motive : Term) (proof : Bool) (converted : (Conv env) n n') :
    (Conv env) (loopBodyType n motive proof) (loopBodyType n' motive proof) := by
  unfold loopBodyType
  exact binary_congr (.pi false) (.refl _)
    (binary_congr (.pi true) (binary_congr .lt (.refl _) (converted.renaming Nat.succ closed)) (.refl _))

theorem loopBodyType_motive_congr (closed : Conversion.Closed env) (n : Term) (proof : Bool) (converted : (Conv env) m m') :
    (Conv env) (loopBodyType n m proof) (loopBodyType n m' proof) := by
  unfold loopBodyType
  exact binary_congr (.pi false) (.refl _) (binary_congr (.pi true) (.refl _)
    (binary_congr (.pi proof) (binary_congr .app (converted.renaming (fun x => x+2) closed) (.refl _))
      (binary_congr .app (converted.renaming (fun x => x+3) closed) (.refl _))))

private theorem list_one (changes : ListRel R [a] ys) : ∃ a', ys = [a'] ∧ R a a' := by
  cases changes with | cons first rest => cases rest; exact ⟨_,rfl,first⟩
private theorem list_two (changes : ListRel R [a,b] ys) :
    ∃ a' b', ys = [a',b'] ∧ R a a' ∧ R b b' := by
  cases changes with | cons first rest =>
    obtain ⟨_,rfl,second⟩ := list_one rest
    exact ⟨_,_,rfl,first,second⟩
private theorem list_three (changes : ListRel R [a,b,c] ys) :
    ∃ a' b' c', ys = [a',b',c'] ∧ R a a' ∧ R b b' ∧ R c c' := by
  cases changes with | cons first rest =>
    obtain ⟨_,_,rfl,second,third⟩ := list_two rest
    exact ⟨_,_,_,rfl,first,second,third⟩
private theorem list_four (changes : ListRel R [a,b,c,d] ys) :
    ∃ a' b' c' d', ys = [a',b',c',d'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' := by
  cases changes with | cons first rest =>
    obtain ⟨_,_,_,rfl,second,third,fourth⟩ := list_three rest
    exact ⟨_,_,_,_,rfl,first,second,third,fourth⟩
private theorem list_five (changes : ListRel R [a,b,c,d,e] ys) :
    ∃ a' b' c' d' e', ys = [a',b',c',d',e'] ∧ R a a' ∧ R b b' ∧ R c c' ∧ R d d' ∧ R e e' := by
  cases changes with | cons first rest =>
    obtain ⟨_,_,_,_,rfl,second,third,fourth,fifth⟩ := list_four rest
    exact ⟨_,_,_,_,_,rfl,first,second,third,fourth,fifth⟩
private theorem list_length (changes : ListRel R xs ys) : xs.length = ys.length := by
  induction changes <;> simp_all
private theorem list_append (changes : ListRel R (xs ++ zs) ys) :
    ∃ xs' zs', ys = xs' ++ zs' ∧ ListRel R xs xs' ∧ ListRel R zs zs' := by
  induction xs generalizing ys with
  | nil => exact ⟨[],ys,rfl,.nil,changes⟩
  | cons x xs ih =>
    cases changes with
    | cons first rest =>
      obtain ⟨xs',zs',rfl,left,right⟩ := ih rest
      exact ⟨_::xs',zs',rfl,.cons first left,right⟩
private theorem list_typed (changes : ListRel (GhostTransform env) xs ys)
    (typed : ∀ x ∈ xs, HasType env loans ctx mode x T) : ∀ y ∈ ys, HasType env [] ctx true y T := by
  induction changes with
  | nil => simp
  | cons first rest ih =>
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact first.typed (typed _ (by simp))
    · exact ih (fun x member => typed x (by simp [member])) y member

private theorem cases_transport (closed : Conversion.Closed env) (branches : Cases env loans ctx motive signatures terms) :
    ∀ terms' motive', ListRel (GhostTransform env) terms terms' → (Conv env) motive motive' →
    Cases env [] ctx motive' signatures terms' := by
  apply Cases.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ ctx motive signatures terms _ =>
      ∀ terms' motive', ListRel (GhostTransform env) terms terms' → (Conv env) motive motive' →
      Cases env [] ctx motive' signatures terms')
    (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i stack ctx motive terms' motive' changes converted
    cases changes
    exact .nil
  case cons =>
    rename_i stack ctx branch signature motive signatures branches typed tail _ ihtail terms' motive' changes converted
    cases changes with
    | cons first rest =>
      exact .cons ((first.typed typed).convert (propCaseType_congr closed signature converted))
        (ihtail _ _ rest converted)

private theorem branch_types_transport (branches : BranchTypes env loans ctx mode types terms) :
    ∀ types' terms', ListRel (Conv env) types types' → ListRel (GhostTransform env) terms terms' →
      BranchTypes env [] ctx true types' terms' := by
  apply BranchTypes.rec (t := branches)
    (motive_1 := fun _ _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ ctx _ types terms _ =>
      ∀ types' terms', ListRel (Conv env) types types' → ListRel (GhostTransform env) terms terms' →
        BranchTypes env [] ctx true types' terms')
  all_goals intros
  all_goals first | trivial | skip
  case nil =>
    rename_i stack ctx mode types' terms' typeChanges termChanges
    cases typeChanges
    cases termChanges
    exact .nil
  case cons =>
    rename_i stack ctx mode branch type types branches typed tail _ ihtail types' terms' typeChanges termChanges
    cases typeChanges with
    | cons changedType restTypes =>
      cases termChanges with
      | cons changedTerm restTerms =>
        exact .cons ((changedTerm.typed typed).convert changedType) (ihtail _ _ restTypes restTerms)

theorem Owned.congr (owned : Owned env A) (converted : (Conv env) A B) : Owned env B := by
  cases owned with
  | buffer related => exact .buffer (.trans (.symm converted) related)
  | family found boxed related => exact .family found boxed (.trans (.symm converted) related)

private theorem viewResult_congr (motive : Conv env a b) (scrutinee : Conv env c d) :
    Conv env (viewResult dependent a c) (viewResult dependent b d) := by
  cases dependent with
  | false => exact motive
  | true => exact binary_congr .app motive scrutinee

private theorem instantiate_congr (closed : Conversion.Closed env) (body : Term) (changed : (Conv env) a b) :
    (Conv env) (body.subst (single a)) (body.subst (single b)) := by
  apply RawLend.Conv.subst_congr closed
  intro index
  cases index with
  | zero => exact changed
  | succ index => exact .refl _

/-- Each child hypothesis comes from forward reduction induction. The output
retains the independently derived original type of the enclosing node. -/
theorem children_preservation (wf : UnifiedProgram.EnvWellFormed env)
    (typed : HasType env loans ctx mode term type) :
    ∀ op xs, term = .node op xs → op ≠ .lend → ∀ ys, ListRel (GhostTransform env) xs ys →
      HasType env [] ctx true (.node op ys) type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun _ ctx _ term type _ =>
      ∀ op xs, term = .node op xs → op ≠ .lend → ∀ ys, ListRel (GhostTransform env) xs ys →
        HasType env [] ctx true (.node op ys) type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | skip
  all_goals rename_i op xs equality notLend ys changes
  case convert source converted ih => exact (ih op xs equality notLend ys changes).convert converted
  all_goals cases equality
  all_goals first | exact False.elim (notLend rfl) | skip
  case univ bound => cases changes; exact .univ bound
  case prop => cases changes; exact .prop
  case u64 => cases changes; exact .u64
  case i64 => cases changes; exact .i64
  case natural bound => cases changes; exact .natural bound
  case integer lower upper => cases changes; exact .integer lower upper
  case array size _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .array (change.typed size)
  case lt left right _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .lt (first.typed left) (second.typed right)
  case eq left right _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .eq (first.typed left) (second.typed right)
  case pi binding body _ _ =>
    obtain ⟨_,_,rfl,domainChange,bodyChange⟩ := list_two changes
    cases binding with
    | intro domain allowed =>
      have binding' := Binder.intro (domainChange.typed domain) (binderAllowed_congr allowed domainChange.converted)
      have body' := (bodyChange.typed body).ghostContext wf
        ((Ghost.ContextConversion.refl env _).extend domainChange.converted _ wf.closed)
      exact .pi binding' body'
  case lam binding body _ _ =>
    obtain ⟨_,_,rfl,domainChange,bodyChange⟩ := list_two changes
    cases binding with
    | intro domain allowed =>
      have binding' := Binder.intro (domainChange.typed domain) (binderAllowed_congr allowed domainChange.converted)
      have body' := (bodyChange.typed body).ghostContext wf
        ((Ghost.ContextConversion.refl env _).extend domainChange.converted _ wf.closed)
      exact (HasType.lam binding' body').convert
        (binary_congr (.pi _) (.symm domainChange.converted) (.refl _))
  case app function argument allowed _ _ =>
    obtain ⟨_,_,rfl,functionChange,argumentChange⟩ := list_two changes
    exact (HasType.app (functionChange.typed function) (by simpa only [Bool.true_or] using argumentChange.typed argument)
      (Or.inl rfl)).convert (instantiate_congr wf.closed _ (.symm argumentChange.converted))
  case uadd left right _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .uadd (first.typed left) (second.typed right)
  case usub left right proof _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    apply HasType.usub (first.typed left) (second.typed right)
    exact (third.typed proof).convert
      (binary_congr .lt second.converted (binary_congr .uadd first.converted (.refl _)))
  case refl value _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact (HasType.refl (change.typed value)).convert
      (binary_congr .eq (.symm change.converted) (.symm change.converted))
  case zeroLe value _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact (HasType.zeroLe (change.typed value)).convert
      (binary_congr .lt (.refl _) (binary_congr .uadd (.symm change.converted) (.refl _)))
  case decide aBound bBound holds =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact (HasType.decideConverted
      (first.typed (HasType.natural (loans := []) (ghost := true) aBound))
      (second.typed (HasType.natural (loans := []) (ghost := true) bBound)) (.symm first.converted) (.symm second.converted)
      aBound bBound holds).convert (binary_congr .lt (.symm first.converted) (.symm second.converted))
  case decideConverted left right leftConv rightConv leftBound rightBound holds _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact (HasType.decideConverted (first.typed left) (second.typed right)
      (.trans (.symm first.converted) leftConv) (.trans (.symm second.converted) rightConv)
      leftBound rightBound holds).convert
      (binary_congr .lt (.symm first.converted) (.symm second.converted))
  case elements size bound values _ =>
    have lengths := list_length changes
    have elements := HasType.elements (lengths.symm.trans size) (lengths ▸ bound) (list_typed changes values)
    simpa only [lengths] using elements
  case index buffer index proof _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact .index (first.typed buffer) (second.typed index)
      ((third.typed proof).convert (binary_congr .lt second.converted (.refl _)))
  case arith left right _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .arith (first.typed left) (second.typed right)
  case strict left right _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .strict (first.typed left) (second.typed right)
  case ltAdd left right step proof _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    exact (HasType.ltAdd (first.typed left) (second.typed right) (third.typed step)
      ((fourth.typed proof).convert (binary_congr .lt first.converted second.converted))).convert
      (binary_congr .lt (binary_congr .uadd (.symm first.converted) (.symm third.converted))
        (binary_congr .uadd (.symm second.converted) (.symm third.converted)))
  case ltCancel left right step proof _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    exact (HasType.ltCancel (first.typed left) (second.typed right) (third.typed step)
      ((fourth.typed proof).convert
        (binary_congr .lt (binary_congr .uadd first.converted third.converted)
          (binary_congr .uadd second.converted third.converted)))).convert
      (binary_congr .lt (.symm first.converted) (.symm second.converted))
  case ltLe left middle right lower upper _ _ _ _ _ =>
    obtain ⟨_,_,_,_,_,rfl,first,second,third,fourth,fifth⟩ := list_five changes
    exact (HasType.ltLe (first.typed left) (second.typed middle) (third.typed right)
      ((fourth.typed lower).convert (binary_congr .lt first.converted second.converted))
      ((fifth.typed upper).convert
        (binary_congr .lt second.converted (binary_congr .uadd third.converted (.refl _))))).convert
      (binary_congr .lt (.symm first.converted) (.symm third.converted))
  case transport motive equality proof _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact (HasType.transport (first.typed motive) (second.typed equality)
      ((third.typed proof).convert (binary_congr .app first.converted (.refl _)))).convert
      (binary_congr .app (.symm first.converted) (.refl _))
  case refine predicate _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .refine (change.typed predicate)
  case pack predicate value proof _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact (HasType.pack (first.typed predicate) (second.typed value)
      ((third.typed proof).convert (binary_congr .app first.converted second.converted))).convert
      (.node .refine (.cons (.symm first.converted) .nil))
  case witness value _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .witness (change.typed value)
  case proof value _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact (HasType.proof (change.typed value)).convert
      (binary_congr .app (.refl _) (.node .witness (.cons (.symm change.converted) .nil)))
  case ifLt left right yes no _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    have yes' := (third.typed yes).ghostContext wf
      ((Ghost.ContextConversion.refl env _).extend (binary_congr .lt first.converted second.converted) true wf.closed)
    exact .ifLt (first.typed left) (second.typed right) yes' (fourth.typed no)
  case ifEq left right yes no _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    have yes' := (third.typed yes).ghostContext wf
      ((Ghost.ContextConversion.refl env _).extend (binary_congr .eq first.converted second.converted) true wf.closed)
    exact .ifEq (first.typed left) (second.typed right) yes' (fourth.typed no)
  case absurd target proof allowed _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact (HasType.absurd (first.typed target) (second.typed proof) (Or.inl rfl)).convert (.symm first.converted)
  case foldI64 count init body allowed _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact .foldI64 (first.typed count) (second.typed init)
      ((third.typed body).convert (foldBodyType_congr wf.closed first.converted)) (Or.inl rfl)
  case foldOwned count init owned body allowed _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact .foldOwned (first.typed count) (second.typed init) owned
      ((third.typed body).convert (foldAccumulatorBodyType_count_congr wf.closed first.converted)) (Or.inl rfl)
  case loop motive motiveAllowed count init body bodyAllowed _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    have init' := (third.typed init).convert (binary_congr .app second.converted (.refl _))
    have body' := (fourth.typed body).convert
      (.trans (loopBodyType_count_congr wf.closed _ _ first.converted) (loopBodyType_motive_congr wf.closed _ _ second.converted))
    exact (HasType.loop (second.typed motive) (Or.inl rfl)
      (by simpa only [Bool.true_or] using first.typed count)
      (by simpa only [Bool.true_or] using init')
      (by simpa only [Bool.true_or] using body') (Or.inl rfl)).convert
      (binary_congr .app (.symm second.converted) (.symm first.converted))
  case global found => cases changes; exact .global found
  case ind found arity size indices _ =>
    exact .ind found arity ((list_length changes).symm.trans size) (list_typed changes indices)
  case con found signature size args _ =>
    exact .con found signature (size.trans (list_length changes)) (arguments_transport wf.closed args _ changes)
  case propElim found proof motive branches scrutinee _ _ _ =>
    cases changes with
    | cons motiveChange remaining =>
      obtain ⟨branches',end',rfl,branchChanges,endChange⟩ := list_append remaining
      obtain ⟨scrutinee',rfl,scrutineeChange⟩ := list_one endChange
      have lengths := list_length branchChanges
      have result := (HasType.propElim (ghost := true) found proof (motiveChange.typed motive)
        (cases_transport wf.closed branches _ _ branchChanges motiveChange.converted) (scrutineeChange.typed scrutinee)).convert
        (applications_motive_congr (.symm motiveChange.converted) _)
      simpa only [lengths] using result
  case dataElim found isData boxed size motive scrutinee generated branches allowed _ _ _ =>
    cases changes with
    | cons motiveChange remaining =>
      obtain ⟨branches',end',rfl,branchChanges,endChange⟩ := list_append remaining
      obtain ⟨scrutinee',rfl,scrutineeChange⟩ := list_one endChange
      obtain ⟨types',generated',typeChanges⟩ := dataCaseTypes_motive_congr wf.closed motiveChange.converted generated
      have lengths := list_length branchChanges
      have result := (HasType.dataElim (ghost := true) found isData boxed size (motiveChange.typed motive)
        (by simpa only [Bool.true_or] using scrutineeChange.typed scrutinee) generated'
        (by simpa only [Bool.true_or] using branch_types_transport branches _ _ typeChanges branchChanges)
        (Or.inl rfl)).convert
        (binary_congr .app (applications_motive_congr (.symm motiveChange.converted) _)
          (.symm scrutineeChange.converted))
      simpa only [lengths] using result
  case drop found boxed owner rest _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .drop found boxed (first.typed owner) (second.typed rest)
  case refOwned owner owned _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .refOwned (change.typed owner) (owned.congr change.converted)
  case codeBorrowOwned owner owned active _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .ghostBorrowOwned (change.typed owner) owned
  case ghostBorrowOwned owner owned _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .ghostBorrowOwned (change.typed owner) owned
  case ghostDerefOwned reference _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .ghostDerefOwned (change.typed reference)
  case view found isData boxed arity size scrutinee motive allowed generated branches _ _ _ =>
    cases changes with
    | cons motiveChange remaining =>
      obtain ⟨branches',end',rfl,branchChanges,endChange⟩ := list_append remaining
      obtain ⟨scrutinee',rfl,scrutineeChange⟩ := list_one endChange
      obtain ⟨types',generated',typeChanges⟩ := viewCaseTypes_motive_congr wf.closed motiveChange.converted generated
      have lengths := list_length branchChanges
      have result := (HasType.view (ghost := true) found isData boxed arity size
        (scrutineeChange.typed scrutinee) (motiveChange.typed motive) (Or.inl rfl) generated'
        (branch_types_transport branches _ _ typeChanges branchChanges)).convert
        (viewResult_congr (.symm motiveChange.converted) (.symm scrutineeChange.converted))
      simpa only [lengths] using result
  case buffer size _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .buffer (change.typed size)
  case alloc size value _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact (HasType.alloc (first.typed size) (second.typed value)).convert
      (.node .buffer (.cons (.symm first.converted) .nil))
  case store buffer index value proof _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    exact .store (first.typed buffer) (second.typed index) (third.typed value)
      ((fourth.typed proof).convert (binary_congr .lt second.converted (.refl _)))
  case load buffer index proof continuation value owner result lowered allowed _ _ _ _ =>
    obtain ⟨_,_,_,_,rfl,first,second,third,fourth⟩ := list_four changes
    exact .load (first.typed buffer) (second.typed index)
      ((third.typed proof).convert (binary_congr .lt second.converted (.refl _)))
      (fourth.typed continuation) value owner result lowered (Or.inl rfl)
  case free buffer rest _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .free (first.typed buffer) (second.typed rest)
  case refBuffer size _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    obtain ⟨_,rfl,kids⟩ := RawLend.Forward.rigid_shape change.forward rfl rfl
    obtain ⟨_,rfl,_⟩ := list_one kids
    exact .refBuffer (change.typed (HasType.buffer (ghost := true) size)).bufferView.1
  case ghostBorrow buffer _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .ghostBorrow (change.typed buffer)
  case ghostDeref reference _ =>
    obtain ⟨_,rfl,change⟩ := list_one changes
    exact .ghostDeref (change.typed reference)
  case borrowedIndex reference index proof _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact .borrowedIndex (first.typed reference) (second.typed index)
      ((third.typed proof).convert (binary_congr .lt second.converted (.refl _)))
  case back owner owned motive representation _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    exact .back (first.typed owner) (owned.congr first.converted)
      ((second.typed motive).convert (binary_congr (.pi false) first.converted (.refl _))) (Or.inl rfl)
  case give owner owned motive representation result _ _ _ =>
    obtain ⟨_,_,_,rfl,first,second,third⟩ := list_three changes
    exact (HasType.give (second.typed owner) owned (first.typed motive) (Or.inl rfl)
      (by simpa only [Bool.true_or] using
        (third.typed result).convert (binary_congr .app first.converted second.converted))).convert
      (binary_congr (.back _) (.refl _) (.symm first.converted))
  case take value continuation declaredOwner declaredResult normalized lowered allowed _ _ =>
    obtain ⟨_,_,rfl,first,second⟩ := list_two changes
    have shape := second.shape
    simp only [LambdaShape] at shape
    obtain ⟨owner',inner',rfl,owners,innerShape⟩ := shape
    obtain ⟨result',body',rfl,results,_⟩ := innerShape
    exact .take (first.typed value) (second.typed continuation)
      (.trans (.symm owners) declaredOwner) (.trans (.symm results) declaredResult)
      normalized lowered (Or.inl rfl)


end Jihoo.NativeKernel.Environment.LoanTyping
