import Jihoo.NativeHigherKindSource
set_option maxUniverseOffset 40

/-! Closed actual source examples at arbitrary higher-kind order and mixed
native universe levels. Concrete model applications compute with genuine
finite Pi beta, rather than assumed output code/normalization certificates. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Examples

def identityExpression (kind : Kind) (valid : kind.Valid) : Expression [] (.arrow kind kind) := .lam valid (.var .here)

theorem identity_typed (wf : UnifiedProgram.EnvWellFormed env) (kind : Kind) (valid : kind.Valid) :
    HasType env [] true (.lam false kind.syntax (.var 0)) (.pi false kind.syntax kind.syntax) :=
  Expression.typed wf (identityExpression kind valid)

theorem identity_application (kind : Kind) (valid : kind.Valid) (value : Finite.Carrier kind.code) :
    (Finite.piMeaning kind.code kind.sort (fun _ => kind.code)).app
      ((identityExpression kind valid).meaning .nil) value = value :=
  (Finite.piMeaning kind.code kind.sort (fun _ => kind.code)).beta _ _

def compositionExpression (A B C : Kind) (validA : A.Valid) (validB : B.Valid) (validC : C.Valid) :
    Expression [] (.arrow (.arrow B C) (.arrow (.arrow A B) (.arrow A C))) :=
  .lam ⟨validB,validC⟩ (.lam ⟨validA,validB⟩ (.lam validA (.app (.var (.there (.there .here))) (.app (.var (.there .here)) (.var .here)))))

theorem composition_typed (wf : UnifiedProgram.EnvWellFormed env) (A B C : Kind) (validA : A.Valid) (validB : B.Valid) (validC : C.Valid) :
    HasType env [] true (compositionExpression A B C validA validB validC).syntax
      (Kind.arrow (.arrow B C) (.arrow (.arrow A B) (.arrow A C))).syntax :=
  Expression.typed wf (compositionExpression A B C validA validB validC)

theorem composition_application (A B C : Kind) (validA : A.Valid) (validB : B.Valid) (validC : C.Valid)
    (function : Finite.Carrier (Kind.arrow B C).code) (argumentFunction : Finite.Carrier (Kind.arrow A B).code)
    (argument : Finite.Carrier A.code) :
    (Finite.piMeaning A.code C.sort (fun _ => C.code)).app
      ((Finite.piMeaning (Kind.arrow A B).code (Kind.arrow A C).sort (fun _ => (Kind.arrow A C).code)).app
        ((Finite.piMeaning (Kind.arrow B C).code (Kind.arrow (.arrow A B) (.arrow A C)).sort
          (fun _ => (Kind.arrow (.arrow A B) (.arrow A C)).code)).app
            ((compositionExpression A B C validA validB validC).meaning .nil) function) argumentFunction) argument =
      (Finite.piMeaning B.code C.sort (fun _ => C.code)).app function
        ((Finite.piMeaning A.code B.sort (fun _ => B.code)).app argumentFunction argument) := by
  simp only [compositionExpression,Expression.meaning,Member.value]
  erw [(Finite.piMeaning (Kind.arrow B C).code (Kind.arrow (.arrow A B) (.arrow A C)).sort
    (fun _ => (Kind.arrow (.arrow A B) (.arrow A C)).code)).beta]
  erw [(Finite.piMeaning (Kind.arrow A B).code (Kind.arrow A C).sort (fun _ => (Kind.arrow A C).code)).beta]
  erw [(Finite.piMeaning A.code C.sort (fun _ => C.code)).beta]

def arrowBuilder (first second : Fin 33) (firstInput : first.val < 32) (secondInput : second.val < 32) :
    Expression [] (.arrow (.base first) (.arrow (.base second) (.base (maxLevel first second)))) :=
  .lam firstInput (.lam secondInput (.arrowCode (.var (.there .here)) (.var .here)))

theorem arrowBuilder_typed (wf : UnifiedProgram.EnvWellFormed env) (first second : Fin 33) (firstInput : first.val < 32) (secondInput : second.val < 32) :
    HasType env [] true (arrowBuilder first second firstInput secondInput).syntax
      (Kind.arrow (.base first) (.arrow (.base second) (.base (maxLevel first second)))).syntax :=
  Expression.typed wf (arrowBuilder first second firstInput secondInput)

theorem arrowBuilder_application (first second : Fin 33) (firstInput : first.val < 32) (secondInput : second.val < 32)
    (domain : Finite.Carrier (Finite.AdministrativeValues.codeUniverse first)) (codomain : Finite.Carrier (Finite.AdministrativeValues.codeUniverse second)) :
    Finite.AdministrativeValues.decode (maxLevel first second)
      ((Finite.piMeaning (Finite.AdministrativeValues.codeUniverse second) (Kind.base (maxLevel first second)).sort
        (fun _ => Finite.AdministrativeValues.codeUniverse (maxLevel first second))).app
          ((Finite.piMeaning (Finite.AdministrativeValues.codeUniverse first)
            (Kind.arrow (.base second) (.base (maxLevel first second))).sort
            (fun _ => (Kind.arrow (.base second) (.base (maxLevel first second))).code)).app
              ((arrowBuilder first second firstInput secondInput).meaning .nil) domain) codomain) =
      Finite.pi (Finite.AdministrativeValues.decode first domain) (.type ⟨second.val,by omega⟩)
        (fun _ => Finite.AdministrativeValues.decode second codomain) := by
  simp only [arrowBuilder,Expression.meaning,Member.value]
  erw [(Finite.piMeaning (Kind.base first).code
    (Kind.arrow (.base second) (.base (maxLevel first second))).sort
    (fun _ => (Kind.arrow (.base second) (.base (maxLevel first second))).code)).beta]
  erw [(Finite.piMeaning (Kind.base second).code (Kind.base (maxLevel first second)).sort
    (fun _ => (Kind.base (maxLevel first second)).code)).beta]
  exact Finite.AdministrativeValues.decode_encode _ _

theorem arrowBuilder_source_reconstruction (wf : UnifiedProgram.EnvWellFormed env) (first second : Fin 33) (firstInput : first.val < 32) (secondInput : second.val < 32) :
    ∃ kind,∃ expression : Expression [] kind,expression.syntax = (arrowBuilder first second firstInput secondInput).syntax ∧
      Conversion.Conv env kind.syntax
        (Kind.arrow (.base first) (.arrow (.base second) (.base (maxLevel first second)))).syntax ∧
      ∀ _values : Values [],Nonempty (Finite.Carrier kind.code) :=
  native_fundamental wf (arrowBuilder_typed wf first second firstInput secondInput) (Expression.recognized _)


def administrativeTop : Expression [] (.base ⟨32,by decide⟩) := .univ ⟨31,by decide⟩

theorem administrative_top_typed (wf : UnifiedProgram.EnvWellFormed env) :
    HasType env [] true (.univ 31) (.univ 32) := Expression.typed wf administrativeTop

theorem administrative_top_decodes :
    Finite.AdministrativeValues.decode ⟨32,by decide⟩ (administrativeTop.meaning .nil) =
      Finite.AdministrativeValues.codeUniverse ⟨31,by decide⟩ := Expression.decode_univ ⟨31,by decide⟩ .nil

theorem administrative_top_not_binder_kind : ¬ (Kind.base ⟨32,by decide⟩).Valid := by
  change ¬ (32 : Nat) < 32
  decide

theorem administrative_pi_typed (wf : UnifiedProgram.EnvWellFormed env) :
    HasType env [] true (.pi false (.univ 31) .u64) (.univ 32) := by
  have typed := Expression.typed wf (Expression.arrowCode administrativeTop (Expression.u64 (kinds := [])))
  simpa only [administrativeTop,Expression.syntax,Term.u64,Term.rename,renameArgs,
    Kind.syntax,maxLevel,Nat.max_zero,context,List.map_nil] using typed

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds.Examples
