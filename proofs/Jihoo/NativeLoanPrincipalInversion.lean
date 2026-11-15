import Jihoo.NativeLoanFunctionInversion
import Jihoo.NativeEnvironmentInversion

/-! Full principal inversion for all 64 loan-indexed typing rules. Lend views
retain the actual generic or specialized source premises; no callback typing
or result typing is invented for a dependent source rule. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping
open _root_.Jihoo.NativeKernel.Environment.LoanTyping.Conversion

inductive LendOrigin (env : Environment) (loans : Loans.Stack) (ctx : Context) :
    Bool → Term → Term → Term → Term → Prop where
  | generic : HasType env loans ctx ghost owner T → Owned env T → Outlived env A →
      HasType env loans ctx ghost reader (.pi false (.ref T) (A.rename Nat.succ)) →
      HasType env loans ctx ghost continuation
        (.pi false A ((Term.pi false T (result.rename Nat.succ)).rename Nat.succ)) →
      continuationAllowed env ghost result →
      LendOrigin env loans ctx ghost owner reader continuation result
  | dependentCode : HasType env loans ctx false (.var owner) T → Owned env T →
      Binder env loans ctx false domain sort → Conversion.Conv env domain (.ref T) →
      HasType env (Loans.enter ctx.length owner loans) ctx false (Lending.read (.var owner) readerBody) A →
      Outlived env A → Conversion.Conv env first A →
      Conversion.Conv env again (T.rename Nat.succ) →
      HasType env loans ctx false (Lending.restore (.var owner) first body) (.pi false first result) →
      Conversion.Conv env result normal → PartialRenaming.shift (-1) 0 normal = some outside →
      continuationAllowed env false outside →
      LendOrigin env loans ctx false (.var owner) (.lam false domain readerBody) (.lam false first (.lam false again body)) outside
  | dependentGhost : HasType env loans ctx true owner T → Owned env T →
      Binder env loans ctx false domain sort → Conversion.Conv env domain (.ref T) →
      HasType env loans ctx true (Lending.read owner readerBody) A →
      Outlived env A → Conversion.Conv env first A →
      Conversion.Conv env again (T.rename Nat.succ) →
      HasType env loans ctx true (Lending.restore owner first body) (.pi false first result) →
      Conversion.Conv env result normal → PartialRenaming.shift (-1) 0 normal = some outside →
      LendOrigin env loans ctx true owner (.lam false domain readerBody) (.lam false first (.lam false again body)) outside

def PrincipalView (env : Environment) (loans : Loans.Stack) (Γ : Context) (mode : Bool) : Term → Term → Prop
  | .var x, T => ∃ b, lookup Γ x = some b ∧ Conv env b.ty T
  | .univ n, T => Conv env (.univ (n+1)) T
  | .prop, T | .u64, T | .i64, T | .array _, T | .refine _, T => Conv env (.univ 0) T
  | .lt _ _, T | .eq _ _, T => Conv env .prop T
  | .natural _, T | .uadd _ _, T | .usub _ _ _, T | .witness _, T => Conv env .u64 T
  | .integer _, T | .index _ _ _, T | .arith _ _ _, T => Conv env .i64 T
  | .elements _ xs, T => Conv env (.array (.natural xs.length)) T
  | .decide a b, T => Conv env (.lt a b) T
  | .refl a, T => Conv env (.eq a a) T
  | .zeroLe a, T => Conv env (.lt (.natural 0) (.uadd a (.natural 1))) T
  | .ltAdd a b c _, T => Conv env (.lt (.uadd a c) (.uadd b c)) T
  | .ltCancel a b _ _, T => Conv env (.lt a b) T
  | .ltLe a _ c _ _, T => Conv env (.lt a c) T
  | .pack p _ _, T => Conv env (.refine p) T
  | .pi e A B, T => ∃ s r : SortTag,
      HasType env loans Γ true A s.term ∧ HasType env loans (⟨A,e⟩ :: Γ) true B r.term ∧ Conv env (s.pi r).term T
  | .lam e A body, T => ∃ B, HasType env loans (⟨A,e⟩ :: Γ) mode body B ∧ Conv env (.pi e A B) T
  | .app f a, T => ∃ e A B, HasType env loans Γ mode f (.pi e A B) ∧ Conv env (B.subst (single a)) T
  | .strict _ b, T => ∃ B, HasType env loans Γ mode b B ∧ Conv env B T
  | .transport f e _, T => ∃ a b, HasType env loans Γ true e (.eq a b) ∧ Conv env (.app f b) T
  | .proof s, T => ∃ p, HasType env loans Γ true s (.refine p) ∧ Conv env (.app p (.witness s)) T
  | .ifLt _ _ _ no, T | .ifEq _ _ _ no, T => ∃ B, HasType env loans Γ mode no B ∧ Conv env B T
  | .absurd U _, T => Conv env U T
  | .fold _ init _, T => ∃ A, HasType env loans Γ mode init A ∧ Conv env A T
  | .loop n motive _ _, T => Conv env (.app motive n) T
  | .node (.global g) [], T => ∃ declaration, env.globals[g]? = some declaration ∧
      Conv env (declaration.type.rename (fun x => x + Γ.length)) T
  | .node (.ind f _) _, T => ∃ entry, env.families[f]? = some entry ∧
      Conv env (if entry.declaration.data then .univ 0 else .prop) T
  | .node (.con f k _) xs, T => ∃ entry signature arity indices,
      env.families[f]? = some entry ∧ entry.signatures[k]? = some signature ∧
      Arguments env loans Γ mode entry.declaration.data
        ((signatureTerm f signature).rename (fun x => x + Γ.length)) xs
        (.node (.ind f arity) indices) ∧ Conv env (.node (.ind f arity) indices) T
  | .node (.elim f count) args, T => ∃ entry motive branches scrutinee indices scrutineeMode,
      env.families[f]? = some entry ∧ count = branches.length ∧
      args = motive :: (branches ++ [scrutinee]) ∧
      HasType env loans Γ scrutineeMode scrutinee (.node (.ind f entry.declaration.arity) indices) ∧
      Conv env (eliminationResult entry motive indices scrutinee) T
  | .buffer _, T | .ref _, T | .back _ _ _, T => Conv env (.univ 0) T
  | .alloc n _, T => Conv env (.buffer n) T
  | .store b _ _ _, T => ∃ n, HasType env loans Γ mode b (.buffer n) ∧ Conv env (.buffer n) T
  | .free _ rest, T => ∃ R, HasType env loans Γ mode rest R ∧ Conv env R T
  | .borrow b, T => ∃ R, HasType env loans Γ true b R ∧ Conv env (.ref R) T
  | .deref r, T => ∃ R, HasType env loans Γ true r (.ref R) ∧ Conv env R T
  | .give e motive owner _, T => ∃ R, HasType env loans Γ mode owner R ∧ Conv env (.back e R motive) T
  | .load _ _ _ continuation, T | .take _ continuation, T =>
      ∃ A e B C normal outside,
      HasType env loans Γ mode continuation (.pi false A (.pi e B C)) ∧
      Conv env C normal ∧ PartialRenaming.shift (-2) 0 normal = some outside ∧ Conv env outside T
  | .node (.caseOf f count) args, T => ∃ entry motive branches scrutinee indices scrutineeMode,
      env.families[f]? = some entry ∧ count = branches.length ∧
      args = motive :: (branches ++ [scrutinee]) ∧
      HasType env loans Γ scrutineeMode scrutinee (.node (.ind f entry.declaration.arity) indices) ∧
      Conv env (eliminationResult entry motive indices scrutinee) T
  | .node (.drop _) [_,rest], T => ∃ R, HasType env loans Γ mode rest R ∧ Conv env R T
  | .node (.view _ family count) fields, T => ∃ entry motive branches scrutinee indices scrutineeMode dependent,
      env.families[family]? = some entry ∧ count = branches.length ∧
      fields = motive :: (branches ++ [scrutinee]) ∧
      HasType env loans Γ scrutineeMode scrutinee (.ref (.node (.ind family entry.declaration.arity) indices)) ∧
      HasType env loans Γ true motive (viewMotiveType dependent (.node (.ind family entry.declaration.arity) indices)) ∧
      Conv env (viewResult dependent motive scrutinee) T
  | .lend owner reader continuation, T => ∃ principal, LendOrigin env loans Γ mode owner reader continuation principal ∧ Conv env principal T
  | _, _ => False

theorem PrincipalView.convert (h : PrincipalView env loans Γ mode t A) (hc : Conv env A B) :
    PrincipalView env loans Γ mode t B := by
  fun_cases PrincipalView env loans Γ mode t A <;> simp only [PrincipalView] at h ⊢
  all_goals first
    | exact False.elim h
    | exact .trans h hc
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l,m⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,j,k,l,.trans m hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,j,k,.trans l hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j,k⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,j,.trans k hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i,j⟩ := h; exact ⟨a,b,c,d,e,f,g,h,i,.trans j hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h,i⟩ := h; exact ⟨a,b,c,d,e,f,g,h,.trans i hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g,h⟩ := h; exact ⟨a,b,c,d,e,f,g,.trans h hc⟩)
    | (obtain ⟨a,b,c,d,e,f,g⟩ := h; exact ⟨a,b,c,d,e,f,.trans g hc⟩)
    | (obtain ⟨a,b,c,d,e,f⟩ := h; exact ⟨a,b,c,d,e,.trans f hc⟩)
    | (obtain ⟨a,b,c,d,e⟩ := h; exact ⟨a,b,c,d,.trans e hc⟩)
    | (obtain ⟨a,b,c,d⟩ := h; exact ⟨a,b,c,.trans d hc⟩)
    | (obtain ⟨a,b,c⟩ := h; exact ⟨a,b,.trans c hc⟩)

theorem HasType.principalView (h : HasType env loans Γ mode t T) : PrincipalView env loans Γ mode t T := by
  apply HasType.rec (t := h) (motive_1 := fun _ _ _ _ _ _ => True)
    (motive_2 := fun stack ctx ghost term type _ => PrincipalView env stack ctx ghost term type)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ _ _ => True) (motive_5 := fun _ _ _ _ _ _ => True)
  all_goals intros
  all_goals first | trivial | exact RawLend.Conv.refl _ | skip
  case var hx readable => exact ⟨_, hx, .refl _⟩
  case pi hA hB _ _ =>
    cases hA with
    | intro typed allowed => exact ⟨_,_,typed,hB,.refl _⟩
  case lam hA hb _ _ => exact ⟨_,hb,.refl _⟩
  case app hf ha allowed _ _ => exact ⟨_,_,_,hf,.refl _⟩
  case strict ha hb _ _ => exact ⟨_,hb,.refl _⟩
  case transport hf he hp _ _ _ => exact ⟨_,_,he,.refl _⟩
  case proof hs _ => exact ⟨_,hs,.refl _⟩
  case ifLt ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case ifEq ha hb hy hn _ _ _ _ => exact ⟨_,hn,.refl _⟩
  case convert ht conv ih => exact ih.convert conv

  case foldI64 n init body allowed _ _ _ => exact ⟨_,init,.refl _⟩
  case global found => exact ⟨_,found,.refl _⟩
  case ind found arity size typed ih => exact ⟨_,found,.refl _⟩
  case con found sigFound size typed ih => exact ⟨_,_,_,_,found,sigFound,typed,.refl _⟩
  case propElim found prop motive branches scrutinee _ _ _ =>
    exact ⟨_,_,_,_,_,_,found,rfl,rfl,scrutinee,by simpa only [eliminationResult,prop,Bool.false_eq_true,↓reduceIte] using RawLend.Conv.refl _⟩
  case foldOwned count init owned body allowed _ _ _ => exact ⟨_,init,.refl _⟩
  case ghostBorrowOwned owner owned _ => exact ⟨_,owner,.refl _⟩
  case ghostDerefOwned reference _ => exact ⟨_,reference,.refl _⟩
  case drop found boxed owner rest _ _ => exact ⟨_,rest,.refl _⟩
  case dataElim found isData boxed size motive scrutinee generated branches allowed ihm ihs ihb =>
    rename_i family entry analysis stack ctx motiveTerm proof ghost scrutineeTerm indices types caseTerms
    cases analysis <;>
      exact ⟨_,_,_,_,_,_,found,rfl,rfl,scrutinee,by simpa only [eliminationResult,isData,↓reduceIte] using RawLend.Conv.refl _⟩
  case view found isData boxed arity size scrutinee motive allowed generated branches _ _ _ =>
    exact ⟨_,_,_,_,_,_,_,found,rfl,rfl,scrutinee,motive,.refl _⟩
  case store buffer index value proof _ _ _ _ => exact ⟨_,buffer,.refl _⟩
  case load buffer index proof continuation value owner result lowered allowed _ _ _ _ =>
    exact ⟨_,_,_,_,_,_,continuation,result,lowered,.refl _⟩
  case free buffer rest _ _ => exact ⟨_,rest,.refl _⟩
  case ghostBorrow buffer _ => exact ⟨_,buffer,.refl _⟩
  case ghostDeref reference _ => exact ⟨_,reference,.refl _⟩
  case give owner owned motive repr result _ _ _ => exact ⟨_,owner,.refl _⟩
  case take value continuation owner result normalized lowered allowed _ _ =>
    exact ⟨_,_,_,_,_,_,continuation,normalized,lowered,.refl _⟩

  case codeBorrowOwned owner owned active _ => exact ⟨_,owner,.refl _⟩
  case lendGeneric owner owned outlived reader continuation allowed _ _ _ =>
    exact ⟨_,.generic owner owned outlived reader continuation allowed,.refl _⟩
  case lendDependentCode owner owned binder domain reader outlived first again continuation normalized shifted allowed _ _ _ _ =>
    exact ⟨_,.dependentCode owner owned binder domain reader outlived first again continuation normalized shifted allowed,.refl _⟩
  case lendDependentGhost owner owned binder domain reader outlived first again continuation normalized shifted _ _ _ _ =>
    exact ⟨_,.dependentGhost owner owned binder domain reader outlived first again continuation normalized shifted,.refl _⟩


theorem HasType.lendView (typed : HasType env loans ctx mode (.lend owner reader continuation) type) :
    ∃ principal,LendOrigin env loans ctx mode owner reader continuation principal ∧ Conversion.Conv env principal type :=
  typed.principalView

end Jihoo.NativeKernel.Environment.LoanTyping
