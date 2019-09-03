(** * Event handlers *)

(** Events types [E, F : Type -> Type] and itree [E ~> itree F]
    form a category. *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Core.ITreeDefinition
     Eq.Eq
     Eq.UpToTaus
     Indexed.Sum
     Indexed.Relation
     Interp.Interp
     Interp.Recursion.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

Set Printing Universes.
Set Universe Polymorphism.
(* end hide *)

(** ** Handler combinators *)

Module Handler.
(** These are defined primarily for documentation. Except for [htrigger],
    it is recommended to use the [CategoryOps] classes instead
    (with the same function names). *)

(** Lift an _event morphism_ into an _event handler_. *)
Definition htrigger@{uE uF uR uT} {A B : Type@{uE} -> Type@{uF}} (m : A ~> B) : A ~> itree@{uE uF uR uT} B :=
  fun _ e => ITree.trigger (m _ e).

(** Trivial handler, triggering any event it's given, so
    the resulting interpretation is the identity function:
    [interp (id_ E) _ t ≈ t]. *)
Definition id_@{uE uF uR uT} (E : Type@{uE} -> Type@{uF}) : E ~> itree@{uE uF uR uT} E := ITree.trigger.

(** Chain handlers: [g] handles the events produced by [f]. *)
Definition cat@{uE uF uR uT} {E F G : Type@{uE} -> Type@{uF}}
           (f : E ~> itree@{uE uF uR uT} F) (g : F ~> itree G)
  : E ~> itree@{uE uF uR uT} G
  := fun R e => interp g (f R e).

(** Wrap events to the left of a sum. *)
Definition inl_@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} : E ~> itree@{uE uF uR uT} (E +' F)
  := htrigger inl1.

(** Wrap events to the right of a sum. *)
Definition inr_@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}} : F ~> itree@{uE uF uR uT} (E +' F)
  := htrigger inr1.

(** Case analysis on sums of events. *)
Definition case_@{uE uF uR uT} {E F G : Type@{uE} -> Type@{uF}}
           (f : E ~> itree@{uE uF uR uT} G) (g : F ~> itree@{uE uF uR uT} G)
  : sum1@{uE uF} E F ~> itree@{uE uF uR uT} G
  := fun _ ab => match ab with
                 | inl1 a => f _ a
                 | inr1 b => g _ b
                 end.

(** Handle events independently, with disjoint sets of output events. *)
Definition bimap@{uE uF uR uT} {E F G H : Type@{uE} -> Type@{uF}}
           (f : E ~> itree G)
           (g : F ~> itree H)
  : (E +' F) ~> itree (G +' H)
  := case_@{uE uF uR uT} (Handler.cat f inl_) (Handler.cat g inr_).

(** Handle [void1] events (of which there are none). *)
Definition empty@{uE uF uR uT} {E : Type@{uE} -> Type@{uF}}
  : void1 ~> itree@{uE uF uR uT} E
  := fun _ e => match e : void1@{uE uF} _ with end.

End Handler.

(** ** Category instances *)

Definition Handler@{uE uF uR uT} (E F : Type@{uE} -> Type@{uF}) := E ~> itree@{uE uF uR uT} F.

Definition handler@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : (E ~> itree@{uE uF uR uT} F) -> Handler E F
  := fun h => h.

Definition eq_Handler@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : Handler@{uE uF uR uT} E F -> Handler E F -> Prop
  := i_pointwise (fun R => eq_itree eq).

Definition eutt_Handler@{uE uF uR uT} {E F : Type@{uE} -> Type@{uF}}
  : Handler E F -> Handler@{uE uF uR uT} E F -> Prop
  := i_pointwise (fun R => eutt eq).

Section Instances.
Universe uE uF uR uT uY.

(** The default handler equivalence is [eutt]. *)
Global Instance Eq2_Handler : Eq2@{uY _} Handler@{uE uF uR uT}
  := @eutt_Handler.

Global Instance Id_Handler : Id_@{uY _} Handler@{uE uF uR uT}
  := @Handler.id_.

Global Instance Cat_Handler : Cat@{uY _} Handler@{uE uF uR uT}
  := @Handler.cat.

Global Instance Case_sum1_Handler : CoprodCase@{uY _} Handler@{uE uF uR uT} sum1
  := @Handler.case_.

Global Instance Inl_sum1_Handler : CoprodInl@{uY _} Handler@{uE uF uR uT} sum1
  := @Handler.inl_.

Global Instance Inr_sum1_Handler : CoprodInr@{uY _} Handler@{uE uF uR uT} sum1
  := @Handler.inr_.

Global Instance Initial_void1_Handler : Initial@{uY _} Handler@{uE uF uR uT} void1
  := @Handler.empty.

Global Instance Iter_Handler : Iter@{uY _} Handler@{uE uF uR uT} sum1
  := @mrec.

End Instances.
