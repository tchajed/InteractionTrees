(** * State *)

(** Events to read and update global state. *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Core.ITreeDefinition
     Indexed.Function
     Indexed.Sum
     Core.Subevent
     Interp.Handler
     Interp.Interp.

Import ITree.Basics.Basics.Monads.
Import ITreeNotations.

Open Scope itree_scope.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Section interp_state.
Universe uE uF uR uT.

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)
Definition interp_state {E : Type@{uE} -> Type@{uF}} {M : Type@{uR} -> Type@{uT}} {S : Type@{uR}}
           {FM : Functor M} {MM : Monad M}
           {IM : MonadIter@{uR uT} M} (h : forall T : Type@{uE}, E T -> stateT@{uR uT} S M T) :
  forall T : Type@{uR}, itree@{uE uF uR uT} E T -> stateT S M T := interp@{uE uF uR uT} h.

End interp_state.

Arguments interp_state {E M S FM MM IM} h [T].

Variant stateE@{uE uF} (S : Type@{uE}) : Type@{uE} -> Type@{uF} :=
| Get : stateE S S
| Put : S -> stateE S unit
.

Arguments Get {S}.
Arguments Put {S}.

Section State.
Universe uE uF uR uT.
Context {S : Type@{uE}} {E : Type@{uE} -> Type@{uF}}.

Definition get `{stateE S -< E} : itree@{uE uF uR uT} E S := embed Get.
Definition put `{stateE S -< E} : S -> itree@{uE uF uR uT} E unit := embed Put.

Definition handle_state
  : forall T : Type@{uE}, stateE@{uE uF} S T -> stateT S (itree@{uE uF uR uT} E) T :=
  fun _ e s =>
    match e with
    | Get => Ret (s, s)
    | Put s' => Ret (s', tt)
    end.

(* SAZ: this is the instance for the hypothetical "Trigger E M" typeclass.
    Class Trigger E M := trigger : E ~> M 
 *)
Definition pure_state
  : forall T : Type@{uE}, E T -> stateT S (itree@{uE uF uR uT} E) T
  := fun _ e s => Vis e (fun x => Ret (s, x)).

End State.

Arguments get {S E _}.
Arguments put {S E _}.

Definition run_state@{uE uF uR uT uY u0 u1} {S : Type@{uE}} {E : Type@{uE} -> Type@{uF}}
  : itree@{uE uF uR uT} (stateE@{uE uF} S +' E) ~> stateT S (itree@{uE uF uR uT} E)
  := interp_state@{_ _ uR uT u0 u1}
       (case_@{uY _} (mk_IFun handle_state@{_ _ uR uT})
                     (mk_IFun pure_state@{_ _ uR uT})).

Arguments run_state {S E} [_] _ _.


(* ----------------------------------------------------------------------- *)
(* SAZ: The code from here to <END> below doesn't belong to State.v  it should 
   go in Prop.v or something like that . *)
(* todo(gmm): this can be stronger if we allow for a `can_returnE` *)
Inductive can_return {E : Type -> Type} {t : Type} : itree E t -> t -> Prop :=
| can_return_Ret {x} : can_return (Ret x) x
| can_return_Tau {tr x} (_ : can_return tr x) : can_return (Tau tr) x
| can_return_Vis {u e k} {x: u} {res} (_ : can_return (k x) res)
  : can_return (Vis e k) res.

(** A propositional "interpreter"
    This can be useful for non-determinism.
 *)
Section interp_prop.
  Context {E F : Type -> Type}.

  Definition eff_hom_prop : Type :=
    forall t, E t -> itree F t -> Prop.

  CoInductive interp_prop (f : eff_hom_prop) (R : Type)
  : itree E R -> itree F R -> Prop :=
  | ipRet : forall x, interp_prop f R (Ret x) (Ret x)
  | ipVis : forall {T} {e : E T} {e' : itree F T}
              (k : _ -> itree E R) (k' : T -> itree F R),
      f _ e e' ->
      (forall x,
          can_return e' x ->
          interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (ITree.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.
(* <END> -------------------------------------------------------------------- *)


(** An extensional stateful handler *)
Section eff_hom_e.
  Context {E F : Type -> Type}.

  (* note(gmm): you should be able to add events here
   * using a monad transformer. In that case, the type
   * of `eval` is:
   *
   *   forall t, E t -> m (itree F) (t * eff_hom_e)
   *
   * but you have the usual conditions on strictly positive uses
   *)
  CoInductive eff_hom_e : Type :=
  { eval : forall t, E t -> itree F (eff_hom_e * t) }.

  Definition interp_e (h : eff_hom_e) : itree E ~> itree F := fun R t =>
    ITree.iter (fun '(s, t) =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl (s, t))
      | VisF e k => ITree.map (fun '(s, x) => inl (s, k x)) (h.(eval) _ e)
      end) (h, t).

End eff_hom_e.


