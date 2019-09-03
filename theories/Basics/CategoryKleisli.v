(* begin hide *)
From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Basics.MonadTheory.

Set Universe Polymorphism.
Set Printing Universes.
(* end hide *)

Definition Kleisli@{uR uT} (m : Type@{uR} -> Type@{uT}) (a b : Type@{uR})
  : Type@{uT} := a -> m b.

(* SAZ: We need to show how these are intended to be used. *)
(** A trick to allow rewriting in pointful contexts. *)
Definition Kleisli_arrow@{uR uT} {m : Type@{uR} -> Type@{uT}} {a b : Type@{uR}}
  : (a -> m b) -> Kleisli@{uR uT} m a b := fun f => f.
Definition Kleisli_apply@{uR uT} {m : Type@{uR} -> Type@{uT}} {a b : Type@{uR}}
  : Kleisli@{uR uT} m a b -> (a -> m b) := fun f => f.

Definition pure@{uR uT} {m : Type@{uR} -> Type@{uT}} `{Monad m} {a b : Type@{uR}} (f : a -> b)
  : Kleisli@{uR uT} m a b :=
  fun x => ret (f x).

Section Instances.
  Universe uR uT uY.
  Context {m : Type@{uR} -> Type@{uT}}.
  Context `{Monad m}.
  Context `{EqM m}.

  Global Instance Eq2_Kleisli : Eq2@{uY _} (Kleisli@{uR uT} m) :=
    fun _ _ => pointwise_relation _ eqm.

  Global Instance Cat_Kleisli : Cat@{uY _} (Kleisli@{uR uT} m) :=
    fun _ _ _ u v x =>
      bind (u x) (fun y => v y).

  Definition map {a b c : Type@{uR}} (g:b -> c) (ab : Kleisli@{uR uT} m a b)
    : Kleisli@{uR uT} m a c
    := @cat@{uY _} Type@{uR} _ _ _ _ _ ab (pure@{uR uT} g).
  
  Global Instance Initial_Kleisli : Initial@{uY _} (Kleisli@{uR uT} m) void :=
    fun _ v => match v : void with end.

  Global Instance Id_Kleisli : Id_@{uY _} (Kleisli@{uR uT} m) :=
    fun _ => pure id.

  Global Instance CoprodCase_Kleisli : CoprodCase@{uY _} (Kleisli@{uR uT} m) sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  Global Instance CoprodInl_Kleisli : CoprodInl@{uY _} (Kleisli@{uR uT} m) sum :=
    fun _ _ => pure inl.

  Global Instance CoprodInr_Kleisli : CoprodInr@{uY _} (Kleisli@{uR uT} m) sum :=
    fun _ _ => pure inr.

  Global Instance Iter_Kleisli `{MonadIter m} : Iter@{uY _} (Kleisli@{uR uT} m) sum :=
    fun a b => Basics.iter.

End Instances.
