(** * Reader *)

(** Immutable environment. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Events.Exception
     Interp.Interp
     Interp.Handler.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Variant readerE@{uE uF} (Env : Type@{uE}) : Type@{uE} -> Type@{uF} :=
| Ask : readerE Env Env.

Arguments Ask {Env}.

Section Reader.
Universe uE uF uR uT.
Context {Env : Type@{uE}} {E : Type@{uE} -> Type@{uF}}.

Definition ask `{readerE Env -< E} : itree@{uE uF uR uT} E Env :=
  trigger Ask.

Definition eval_reader : Env -> Handler@{uE uF uR uT} (readerE@{uE uF} Env) E :=
  fun r _ e =>
    match e with
    | Ask => Ret r
    end.

End Reader.

Arguments ask {Env E _}.

Definition run_reader {Env E} : Env -> itree (readerE Env +' E) ~> itree E
  := fun r => interp (case_ (eval_reader r) (id_ _)).

Arguments run_reader {Env E} _ [_] _.
