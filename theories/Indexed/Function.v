(** * The Category of Indexed Functions *)

(** Indexed functions have type [E ~> F], i.e., [forall T, E T -> F T],
    for some [E] and [F]. Like regular functions ([Basics.Function]),
    they form a cocartesian category. *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Category
     Indexed.Relation
     Indexed.Sum.

Set Universe Polymorphism.
(* end hide *)

(** The name of the category. *)
Definition IFun@{u v} (E F : Type@{u} -> Type@{v}) : Type@{max(u+1,v)}
  := forall T : Type@{u}, E T -> F T.

Definition mk_IFun@{u v} {E F : Type@{u} -> Type@{v}}
  : (E ~> F) -> IFun@{u v} E F
  := fun x => x.

(** Unwrap [IFun], potentially useful for type inference. *)
Definition apply_IFun@{u v} {E F T} (f : IFun@{u v} E F) : E T -> F T := f T.

(** Equivalence of indexed functions is extensional equality. *)
Instance Eq2_IFun@{u v uY uZ} : Eq2@{uY uZ} IFun@{u v} :=
  fun E F => i_pointwise (fun T => @eq (F T)).

(** The identity function. *)
Instance Id_IFun@{u v uY uZ} : Id_@{uY uZ} IFun@{u v} :=
  fun E _ e => e.

(** Function composition. *)
Instance Cat_IFun@{u v uY uZ} : Cat@{uY uZ} IFun@{u v} :=
  fun E F G f1 f2 R e => f2 _ (f1 _ e).

(** [void1] is the initial object. *)
Instance Initial_void1@{u v uY uZ} : Initial@{uY uZ} IFun@{u v} void1@{u v} :=
  fun _ _ v => match v : void1 _ with end.

(** The coproduct is case analysis on sums. *)
Definition case_sum1@{u v} {A B C : Type@{u} -> Type@{v}} (f : A ~> C) (g : B ~> C)
  : sum1@{u v} A B ~> C
  := fun _ ab =>
       match ab with
       | inl1 a => f _ a
       | inr1 b => g _ b
       end.

Instance Case_sum1@{u v uY uZ} : CoprodCase@{uY uZ} IFun@{u v} sum1 := @case_sum1.
Instance Inl_sum1@{u v uY uZ} : CoprodInl@{uY uZ} IFun@{u v} sum1 := @inl1.
Instance Inr_sum1@{u v uY uZ} : CoprodInr@{uY uZ} IFun@{u v} sum1 := @inr1.
