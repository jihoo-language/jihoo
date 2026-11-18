import Jihoo.NativeLoanTyping
import Jihoo.NativeEnvironmentExtension

/-! Later global and family entries preserve Loan64 typing, including the
active loans and source-specialized callback judgments of dependent Lend. -/
namespace Jihoo.NativeKernel.Environment.LoanTyping

private theorem binder_allowed_extend (extension : Extends before after)
    (allowed : binderAllowed before erased domain sort) : binderAllowed after erased domain sort := by
  rcases allowed with allowed | ⟨erased, family, count, indices, entry, found, data, converted⟩
  · apply Or.inl
    cases erased with
    | false => exact allowed
    | true => exact allowed.imp id (fun converted => converted.extend extension)
  · exact Or.inr ⟨erased, family, count, indices, entry, extension.families _ _ found,
      data, converted.extend extension⟩

private theorem application_allowed_extend (extension : Extends before after)
    (allowed : applicationAllowed before mode domain argument) : applicationAllowed after mode domain argument := by
  rcases allowed with ghost | ⟨normal,converted,free,representation⟩
  · exact Or.inl ghost
  · refine Or.inr ⟨normal,converted.extend extension,free,?_⟩
    rcases representation with nonKind | ⟨firstOrder,value,valueConverted,plain⟩
    · exact Or.inl nonKind
    · exact Or.inr ⟨firstOrder,value,valueConverted.extend extension,Environment.plain.extend extension plain⟩

private theorem owned_extend (extension : Extends before after)
    (owned : Owned before type) : Owned after type := by
  cases owned with
  | buffer converted => exact .buffer (converted.extend extension)
  | family found boxed converted => exact .family (extension.families _ _ found) boxed (converted.extend extension)

private theorem back_representation_extend (extension : Extends before after)
    (represented : BackRepresentation before mode erased motive) : BackRepresentation after mode erased motive := by
  rcases represented with ghost | erased | ⟨flag,domain,body,converted,fixed⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl erased)
  · exact Or.inr (Or.inr ⟨flag,domain,body,converted.extend extension,
      Environment.fixedRepresentation.extend extension fixed⟩)

private theorem iteration_motive_extend (extension : Extends before after)
    (allowed : IterationMotiveAllowed before mode proof motive) : IterationMotiveAllowed after mode proof motive := by
  rcases allowed with ghost | proof | ⟨normal,converted,scalar⟩ | ⟨erased,domain,body,converted,owned⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl proof)
  · exact Or.inr (Or.inr (Or.inl ⟨normal,converted.extend extension,scalar⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨erased,domain,body,converted.extend extension,owned_extend extension owned⟩))

private theorem view_motive_extend (extension : Extends before after)
    (allowed : ViewMotiveAllowed before mode dependent motive) : ViewMotiveAllowed after mode dependent motive := by
  rcases allowed with ghost | constant | ⟨erased,domain,body,converted,representation⟩
  · exact Or.inl ghost
  · exact Or.inr (Or.inl constant)
  · exact Or.inr (Or.inr ⟨erased,domain,body,converted.extend extension,representation⟩)

private theorem outlived_head_extend (extension : Extends before after)
    (allowed : Lending.outlivedHead before term = true) : Lending.outlivedHead after term = true := by
  cases term with
  | var => exact allowed
  | node op args =>
      cases op <;> try exact allowed
      case ind family count =>
        cases found : before.families[family]? with
        | none => simp [Lending.outlivedHead,found] at allowed
        | some entry =>
            have data : entry.declaration.data = true := by
              simpa only [Lending.outlivedHead,found,Option.any_some] using allowed
            simpa only [Lending.outlivedHead,extension.families _ _ found,Option.any_some] using data
      all_goals
        cases args with
        | nil => exact allowed
        | cons first tail =>
            cases tail with
            | nil => exact allowed
            | cons second tail =>
                cases tail with
                | nil => exact allowed
                | cons third tail => cases tail <;> exact allowed

private theorem outlived_extend (extension : Extends before after)
    (allowed : Outlived before type) : Outlived after type := by
  obtain ⟨normal,converted,head⟩ := allowed
  exact ⟨normal,converted.extend extension,outlived_head_extend extension head⟩

/-- Appending available declarations preserves the exact term, type, mode and
loan stack of every Loan64 derivation. Conversion and positive source policies
reuse their witnesses in the larger environment. -/
theorem HasType.extend (extension : Extends before after)
    (typed : HasType before loans ctx mode term type) : HasType after loans ctx mode term type := by
  apply HasType.rec (t := typed)
    (motive_1 := fun loans ctx erased domain sort _ => Binder after loans ctx erased domain sort)
    (motive_2 := fun loans ctx mode term type _ => HasType after loans ctx mode term type)
    (motive_3 := fun loans ctx mode data telescope arguments result _ =>
      Arguments after loans ctx mode data telescope arguments result)
    (motive_4 := fun loans ctx motive signatures branches _ => Cases after loans ctx motive signatures branches)
    (motive_5 := fun loans ctx mode types branches _ => BranchTypes after loans ctx mode types branches)
  all_goals intros
  case intro _ allowed formed => exact .intro formed (binder_allowed_extend extension allowed)
  case var => exact .var (by assumption) (by assumption)
  case univ => exact .univ (by assumption)
  case prop => exact .prop
  case u64 => exact .u64
  case i64 => exact .i64
  case natural => exact .natural (by assumption)
  case integer => exact .integer (by assumption) (by assumption)
  case array => exact .array (by assumption)
  case lt => exact .lt (by assumption) (by assumption)
  case eq => exact .eq (by assumption) (by assumption)
  case pi => exact .pi (by assumption) (by assumption)
  case lam => exact .lam (by assumption) (by assumption)
  case uadd => exact .uadd (by assumption) (by assumption)
  case usub => exact .usub (by assumption) (by assumption) (by assumption)
  case refl => exact .refl (by assumption)
  case zeroLe => exact .zeroLe (by assumption)
  case decide => exact .decide (by assumption) (by assumption) (by assumption)
  case elements => exact .elements (by assumption) (by assumption) (by assumption)
  case index => exact .index (by assumption) (by assumption) (by assumption)
  case arith => exact .arith (by assumption) (by assumption)
  case strict => exact .strict (by assumption) (by assumption)
  case ltAdd => exact .ltAdd (by assumption) (by assumption) (by assumption) (by assumption)
  case ltCancel => exact .ltCancel (by assumption) (by assumption) (by assumption) (by assumption)
  case ltLe => exact .ltLe (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  case transport => exact .transport (by assumption) (by assumption) (by assumption)
  case refine => exact .refine (by assumption)
  case pack => exact .pack (by assumption) (by assumption) (by assumption)
  case witness => exact .witness (by assumption)
  case proof => exact .proof (by assumption)
  case ifLt => exact .ifLt (by assumption) (by assumption) (by assumption) (by assumption)
  case ifEq => exact .ifEq (by assumption) (by assumption) (by assumption) (by assumption)
  case buffer => exact .buffer (by assumption)
  case alloc => exact .alloc (by assumption) (by assumption)
  case store => exact .store (by assumption) (by assumption) (by assumption) (by assumption)
  case free => exact .free (by assumption) (by assumption)
  case refBuffer => exact .refBuffer (by assumption)
  case ghostBorrow => exact .ghostBorrow (by assumption)
  case ghostDeref => exact .ghostDeref (by assumption)
  case borrowedIndex => exact .borrowedIndex (by assumption) (by assumption) (by assumption)
  case ghostDerefOwned => exact .ghostDerefOwned (by assumption)
  case app _ _ allowed function argument => exact .app function argument (application_allowed_extend extension allowed)
  case decideConverted _ _ left right m n less leftTyped rightTyped =>
      exact .decideConverted leftTyped rightTyped (left.extend extension) (right.extend extension) m n less
  case absurd _ _ allowed result proof =>
      exact .absurd result proof (allowed.imp id (fun positive => positive.extend extension))
  case foldI64 _ _ _ allowed count initial body =>
      exact .foldI64 count initial body (Environment.IterationBodyAllowed.extend extension allowed)
  case foldOwned _ _ owned _ allowed count initial body =>
      exact .foldOwned count initial (owned_extend extension owned) body
        (Environment.IterationBodyAllowed.extend extension allowed)
  case loop _ motiveAllowed _ _ _ bodyAllowed motive count initial body =>
      exact .loop motive (iteration_motive_extend extension motiveAllowed) count initial body
        (Environment.IterationBodyAllowed.extend extension bodyAllowed)
  case global found => exact .global (extension.globals _ _ found)
  case ind found arity size _ indices => exact .ind (extension.families _ _ found) arity size indices
  case con found signature size _ arguments => exact .con (extension.families _ _ found) signature size arguments
  case propElim found prop _ _ _ motive cases scrutinee =>
      exact .propElim (extension.families _ _ found) prop motive cases scrutinee
  case load _ _ _ _ value owner normalized lowered allowed buffer index proof continuation =>
      exact .load buffer index proof continuation (value.extend extension) (owner.extend extension)
        (normalized.extend extension) lowered (allowed.imp id (fun positive => positive.extend extension))
  case back _ owned _ represented owner motive =>
      exact .back owner (owned_extend extension owned) motive (back_representation_extend extension represented)
  case give _ owned _ represented _ owner motive result =>
      exact .give owner (owned_extend extension owned) motive (back_representation_extend extension represented) result
  case take _ _ owner result normalized lowered allowed packed continuation =>
      exact .take packed continuation (owner.extend extension) (result.extend extension) (normalized.extend extension)
        lowered (allowed.imp id (fun positive => positive.extend extension))
  case dataElim found data boxed size _ _ generated _ allowed motive scrutinee branches =>
      exact .dataElim (extension.families _ _ found) data boxed size motive scrutinee generated branches
        (allowed.imp id (fun positive => positive.extend extension))
  case drop found boxed _ _ owner rest => exact .drop (extension.families _ _ found) boxed owner rest
  case refOwned _ owned owner => exact .refOwned owner (owned_extend extension owned)
  case ghostBorrowOwned _ owned owner => exact .ghostBorrowOwned owner (owned_extend extension owned)
  case view found data boxed arity size _ _ allowed generated _ scrutinee motive branches =>
      exact .view (extension.families _ _ found) data boxed arity size scrutinee motive
        (view_motive_extend extension allowed) (Environment.viewCaseTypes_extend extension generated) branches
  case codeBorrowOwned _ owned active owner => exact .codeBorrowOwned owner (owned_extend extension owned) active
  case lendGeneric _ owned outlived _ _ allowed owner reader continuation =>
      exact .lendGeneric owner (owned_extend extension owned) (outlived_extend extension outlived) reader
        continuation (allowed.imp id (fun positive => positive.extend extension))
  case lendDependentCode _ owned _ domain _ outlived first again _ normalized lowered allowed owner binder reader continuation =>
      exact .lendDependentCode owner (owned_extend extension owned) binder (domain.extend extension) reader
        (outlived_extend extension outlived) (first.extend extension) (again.extend extension) continuation
        (normalized.extend extension) lowered (allowed.imp id (fun positive => positive.extend extension))
  case lendDependentGhost _ owned _ domain _ outlived first again _ normalized lowered owner binder reader continuation =>
      exact .lendDependentGhost owner (owned_extend extension owned) binder (domain.extend extension) reader
        (outlived_extend extension outlived) (first.extend extension) (again.extend extension) continuation
        (normalized.extend extension) lowered
  case convert _ converted typed => exact .convert typed (converted.extend extension)
  all_goals first
    | exact Arguments.nil ((show Conversion.Conv before _ _ from by assumption).extend extension)
    | exact Arguments.cons ((show Conversion.Conv before _ _ from by assumption).extend extension)
        (by assumption) (by assumption)
    | exact Cases.nil
    | exact Cases.cons (by assumption) (by assumption)
    | exact BranchTypes.nil
    | exact BranchTypes.cons (by assumption) (by assumption)

end Jihoo.NativeKernel.Environment.LoanTyping
