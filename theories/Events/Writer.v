(** * Writer *)

(** Output events. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     List.
Import ListNotations.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Indexed.Function
     Core.Subevent
     Interp.Interp
     Interp.Handler
     Events.State.

Import Basics.Basics.Monads.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

(** Event to output values of type [W]. *)
Variant writerE@{uE uF} (W : Type@{uE}) : Type@{uE} -> Type@{uF} :=
| Tell : W -> writerE W unit.

(** Output action. *)
Definition tell {W E} `{writerE W -< E} : W -> itree E unit :=
  fun w => trigger (Tell w).

(** One interpretation is to accumulate outputs in a list. *)

(** Note that this handler appends new outputs to the front of the list. *)
Definition handle_writer_list@{uE uF uR uT} {W E}
  : writerE@{uE uF} W ~> stateT (list W) (itree@{uE uF uR uT} E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (w :: s, tt)
       end.

Definition run_writer_list_state@{uE uF uR uT uY u0 u1} {W : Type@{uE}} {E : Type@{uE} -> Type@{uF}}
  : itree (writerE W +' E) ~> stateT (list W) (itree E)
  := interp_state@{uE uF uR uT u0 u1}
       (case_@{uY uT} (mk_IFun handle_writer_list@{_ _ uR uT})
                      (mk_IFun pure_state@{_ _ uR uT})).

Arguments run_writer_list_state {W E} [T].

(** Returns the outputs in order: the first output at the head, the last
    output and the end of the list. *)
Definition run_writer_list {W E}
  : itree (writerE W +' E) ~> writerT (list W) (itree E)
  := fun _ t =>
       ITree.map (fun wsx => (rev' (fst wsx), snd wsx))
                 (run_writer_list_state t []).

Arguments run_writer_list {W E} [T].

(** When [W] is a monoid, we can also use that to append the outputs together. *)

Definition handle_writer@{uE uF uR uT} {W E} (Monoid_W : Monoid W)
  : writerE@{uE uF} W ~> stateT W (itree@{uE uF uR uT} E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (monoid_plus@{uE} Monoid_W s w, tt)
       end.

Definition run_writer@{uE uF uR uT uY u0 u1} {W E} (Monoid_W : Monoid W)
  : itree (writerE W +' E) ~> writerT W (itree E)
  := fun _ t =>
       interp_state@{uE uF uR uT u0 u1}
         (case_@{uY uT} (mk_IFun (handle_writer@{_ _ uR uT} Monoid_W))
                        (mk_IFun pure_state@{_ _ uR uT})) t
         (monoid_unit Monoid_W).

Arguments run_writer {W E} Monoid_W [T].
