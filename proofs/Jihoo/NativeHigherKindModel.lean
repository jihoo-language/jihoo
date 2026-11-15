import Jihoo.NativeHigherKindSyntax
set_option maxUniverseOffset 40

/-! Concrete type-level lambda/application values at arbitrary higher kind,
with any finite interleaving of kind variables. Primitive type codes use the
existing finite Tarski universes and genuine Pi function interpretation. -/
namespace Jihoo.NativeKernel.Environment.Semantics.HigherKinds
open Jihoo.NativeKernel.Environment.Conversion

inductive Values : List Kind → Type 34 where
  | nil : Values []
  | cons : Finite.Carrier kind.code → Values rest → Values (kind :: rest)

def Member.value (member : Member kind kinds index) (values : Values kinds) : Finite.Carrier kind.code :=
  match member,values with
  | .here,.cons value _ => value
  | .there previous,.cons _ rest => previous.value rest

def maxLevel (first second : Fin 33) : Fin 33 := ⟨max first.val second.val,Nat.max_lt.mpr ⟨first.isLt,second.isLt⟩⟩

inductive Expression : List Kind → Kind → Type where
  | var : Member kind kinds index → Expression kinds kind
  | u64 : Expression kinds (.base ⟨0,by decide⟩)
  | univ (level : Fin 32) : Expression kinds (.base ⟨level.val+1,by omega⟩)
  | lam : domain.Valid → Expression (domain :: kinds) codomain → Expression kinds (.arrow domain codomain)
  | app : Expression kinds (.arrow domain codomain) → Expression kinds domain → Expression kinds codomain
  | arrowCode : Expression kinds (.base first) → Expression kinds (.base second) → Expression kinds (.base (maxLevel first second))

def Expression.syntax : Expression kinds kind → Term
  | .var (index := index) _ => .var index
  | .u64 => .u64
  | .univ level => .univ level.val
  | .lam (domain := domain) _ body => .lam false domain.syntax body.syntax
  | .app function argument => .app function.syntax argument.syntax
  | .arrowCode domain codomain => .pi false domain.syntax (codomain.syntax.rename Nat.succ)

def Expression.meaning : Expression kinds kind → Values kinds → Finite.Carrier kind.code
  | .var member,values => member.value values
  | .u64,_ => Finite.AdministrativeValues.encode ⟨0,by decide⟩ Finite.natural
  | .univ level,_ => Finite.AdministrativeValues.encode ⟨level.val+1,by omega⟩
      (Finite.AdministrativeValues.codeUniverse ⟨level.val,by omega⟩)
  | .lam (domain := domain) (codomain := codomain) _ body,values =>
      (Finite.piMeaning domain.code codomain.sort (fun _ => codomain.code)).lam
        (fun argument => body.meaning (.cons argument values))
  | .app (domain := domain) (codomain := codomain) function argument,values =>
      (Finite.piMeaning domain.code codomain.sort (fun _ => codomain.code)).app
        (function.meaning values) (argument.meaning values)
  | .arrowCode (first := first) (second := second) domain codomain,values =>
      Finite.AdministrativeValues.encode (maxLevel first second)
        (Finite.pi (Finite.AdministrativeValues.decode first (domain.meaning values)) (.type ⟨second.val,by omega⟩)
          (fun _ => Finite.AdministrativeValues.decode second (codomain.meaning values)))

theorem Expression.typed (wf : UnifiedProgram.EnvWellFormed env) (expression : Expression kinds kind) :
    HasType env (context kinds) true expression.syntax kind.syntax := by
  induction expression with
  | var member => exact .var member.lookup (Or.inl rfl)
  | u64 => exact .u64
  | univ level => exact .univ (by have := level.isLt; omega)
  | @lam domain kinds codomain valid body ih =>
    exact .lam (.intro (s := .type domain.nativeLevel) (domain.formed valid) (Or.inl (by intro h; cases h))) ih
  | @app kinds domain codomain function argument ihf iha =>
    simpa only [Expression.syntax,Kind.syntax_subst] using HasType.app ihf iha (Or.inl rfl)
  | @arrowCode kinds first second domain codomain hd hc =>
    exact .pi (s := .type first.val) (r := .type second.val)
      (.intro hd (Or.inl (by intro h; cases h)))
      (by simpa only [Kind.syntax,Term.univ,Term.rename,renameArgs,SortTag.term] using hc.ghostWeaken wf domain.syntax false)

theorem Expression.beta (valid : domain.Valid) (body : Expression (domain :: kinds) codomain) (argument : Expression kinds domain)
    (values : Values kinds) :
    (Expression.app (.lam valid body) argument).meaning values = body.meaning (.cons (argument.meaning values) values) :=
  (Finite.piMeaning domain.code codomain.sort (fun _ => codomain.code)).beta _ _

theorem Expression.decode_u64 (values : Values kinds) :
    Finite.AdministrativeValues.decode ⟨0,by decide⟩ ((Expression.u64 (kinds := kinds)).meaning values) = Finite.natural :=
  Finite.AdministrativeValues.decode_encode _ _

theorem Expression.decode_univ (level : Fin 32) (values : Values kinds) :
    Finite.AdministrativeValues.decode ⟨level.val+1,by omega⟩ ((Expression.univ level).meaning values) =
      Finite.AdministrativeValues.codeUniverse ⟨level.val,by omega⟩ := Finite.AdministrativeValues.decode_encode _ _

theorem Expression.decode_arrowCode (domain : Expression kinds (.base first)) (codomain : Expression kinds (.base second))
    (values : Values kinds) :
    Finite.AdministrativeValues.decode (maxLevel first second) ((Expression.arrowCode domain codomain).meaning values) =
      Finite.pi (Finite.AdministrativeValues.decode first (domain.meaning values)) (.type ⟨second.val,by omega⟩)
        (fun _ => Finite.AdministrativeValues.decode second (codomain.meaning values)) := Finite.AdministrativeValues.decode_encode _ _

end Jihoo.NativeKernel.Environment.Semantics.HigherKinds
