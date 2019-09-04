(** * Mutable map *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     String List.
Import ListNotations.

From ExtLib Require Import
     Core.RelDec.

From ExtLib.Structures Require
     Functor Monoid Maps.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Function
     Indexed.Sum
     Core.Subevent
     Interp.Interp
     Events.State.

Import ITree.Basics.Basics.Monads.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Variant mapE@{uE uF} (K V : Type@{uE}) : Type@{uE} -> Type@{uF} :=
| Insert : K -> V -> mapE K V unit
| Lookup : K -> mapE K V (option V)
| Remove : K -> mapE K V unit
.

Arguments Insert {K V}.
Arguments Lookup {K V}.
Arguments Remove {K V}.

Section Map.

Universe uE uF uR uT.
Context {K V : Type@{uE}} {E : Type@{uE} -> Type@{uF}}.

Definition insert `{mapE K V -< E} : K -> V -> itree@{uE uF uR uT} E unit := embed Insert.
Definition lookup `{mapE K V -< E} : K -> itree@{uE uF uR uT} E (option V) := embed Lookup.
Definition remove `{mapE K V -< E} : K -> itree@{uE uF uR uT} E unit := embed Remove.

Definition lookup_def `{mapE K V -< E} : K -> V -> itree@{uE uF uR uT} E V
  := fun k v =>
       ITree.bind (lookup k) (fun ov =>
       Ret (match ov with
            | None => v
            | Some v' => v'
            end)).

End Map.

Section RunMap.

Import Structures.Maps.

Universe uE uF uR uT uM.
Context {K V : Type@{uE}} {map : Type@{uM}}.
Context {M : Map K V map}.
Context {E : Type@{uE} -> Type@{uF}}.

Definition handle_map
  : forall T : Type@{uE}, mapE@{uE uF} K V T -> stateT map (itree@{uE uF uR uT} E) T :=
  fun _ e env =>
    match e with
    | Insert k v => Ret (Maps.add k v env, tt)
    | Lookup k => Ret (env, Maps.lookup k env)
    | Remove k => Ret (Maps.remove k env, tt)
    end.

Definition run_map : itree (mapE K V +' E) ~> stateT map (itree E) :=
  interp_state@{uE uF uR uT _ _} (case_ (mk_IFun handle_map) (mk_IFun pure_state@{_ _ uR uT})).

End RunMap.

Arguments insert {K V E _}.
Arguments lookup {K V E _}.
Arguments remove {K V E _}.
Arguments lookup_def {K V E _}.
Arguments run_map {K V map M E} [T].
