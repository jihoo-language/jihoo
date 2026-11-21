import Jihoo.NativeCorePureComputationNormal
import Jihoo.NativeCodePolicyRenaming

/-! The graph postprocessing rules preserve the global-free predicate.
Beta may introduce a normalized argument in multiple places, but cannot
introduce a transparent reference absent from both source operands. -/
namespace Jihoo.NativeKernel.NativeCoreGlobalFreeComputation

open Environment GlobalEnvironment

private theorem lift_global_free (values : ∀ index, GlobalFree (σ index)) (depth : Nat) :
    ∀ index, GlobalFree (liftSub depth σ index) := by
  induction depth with
  | zero => exact values
  | succ depth ih =>
    intro index
    cases index with
    | zero => simp only [liftSub,liftSubOne,GlobalFree]
    | succ index =>
      change GlobalFree ((liftSub depth σ index).rename Nat.succ)
      exact (globalFree_correct _).mp (by rw [globalFree_rename]; exact (globalFree_correct _).mpr (ih index))

private theorem in_substitution (term : Term) (free : GlobalFree term) (values : ∀ index, GlobalFree (σ index)) :
    GlobalFree (term.subst σ) := by
  induction term using Term.rec
    (motive_2 := fun terms => ∀ op offset σ, (∀ term ∈ terms, GlobalFree term) →
      (∀ index, GlobalFree (σ index)) → ∀ residual ∈ substArgs op σ offset terms, GlobalFree residual)
    generalizing σ with
  | var index => simpa only [Term.subst] using values index
  | node op terms ih =>
    simp only [GlobalFree,Term.subst] at free ⊢
    exact ⟨free.1,ih op 0 σ free.2 values⟩
  | nil =>
    rename_i member
    simp only [substArgs,List.not_mem_nil] at member
  | cons first rest head tail =>
    rename_i op offset substitution supported values residual found
    simp only [substArgs,List.mem_cons] at found
    rcases found with rfl | found
    · exact head (supported first (.head _)) (lift_global_free values _)
    · exact tail op (offset+1) substitution (fun term member => supported term (.tail _ member)) values residual found

private theorem single_global_free (valueFree : GlobalFree value) (index : Nat) :
    GlobalFree (single value index) := by
  cases index with
  | zero => exact valueFree
  | succ index => simp only [single,GlobalFree]

private theorem global_child (free : GlobalFree (.node op terms)) :
    ∀ term ∈ terms, GlobalFree term := by
  rw [GlobalFree] at free
  exact free.2

theorem computes_preserves (step : ACU.Computes source output) (free : GlobalFree source) :
    GlobalFree output := by
  cases step with
  | beta flag A body argument =>
    have lam := global_child free _ (List.Mem.head _)
    have arg := global_child free _ (List.Mem.tail _ (List.Mem.head _))
    exact in_substitution body (global_child lam _ (List.Mem.tail _ (List.Mem.head _))) (single_global_free arg)
  | sub => simp [Term.natural,GlobalFree,ordinary]
  | read count xs index proof value found =>
    have array := global_child free _ (List.Mem.head _)
    exact global_child array _ (List.mem_of_getElem? found)
  | witnessPack =>
    have packed := global_child free _ (List.Mem.head _)
    exact global_child packed _ (List.Mem.tail _ (List.Mem.head _))
  | proofPack =>
    have packed := global_child free _ (List.Mem.head _)
    exact global_child packed _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | derefBorrow | borrowDeref =>
    exact global_child (global_child free _ (List.Mem.head _)) _ (List.Mem.head _)
  | transportRefl =>
    exact global_child free _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  | ifLtTrue m n yes no =>
    have arm := global_child free _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact in_substitution yes arm (single_global_free (by simp [GlobalFree,ordinary,Term.decide,Term.natural]))
  | ifEqTrue n yes no =>
    have arm := global_child free _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    exact in_substitution yes arm (single_global_free (by simp [GlobalFree,ordinary,Term.refl,Term.natural]))
  | ifLtFalse | ifEqFalse =>
    exact global_child free _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem post_rules : NativeCorePureComputationNormal.Rules (fun source output => GlobalFree source → GlobalFree output) := by
  refine ⟨fun _ => id,fun first second => second ∘ first,computes_preserves,?_⟩
  intro op source output _ ordinary changes free
  rw [GlobalFree] at free ⊢
  refine ⟨ordinary,?_⟩
  have all {source output} (changes : NativeKernel.Conversion.ListRel (fun a b => GlobalFree a → GlobalFree b) source output) :
      (∀ term ∈ source, GlobalFree term) → ∀ term ∈ output, GlobalFree term := by
    induction changes with
    | nil => simp
    | cons head _ ih =>
      intro free term found
      rcases List.mem_cons.mp found with rfl | found
      · exact head (free _ (.head _))
      · exact ih (fun t member => free t (.tail _ member)) term found
  exact all changes free.2

end Jihoo.NativeKernel.NativeCoreGlobalFreeComputation
