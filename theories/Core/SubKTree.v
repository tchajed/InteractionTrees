(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.Function
     Basics.FunctionFacts
     Basics.Category
     ITree
     KTree
     KTreeFacts
     Eq.UpToTaus.
From Coq Require Import
     Morphisms.

Import CatNotations.
Local Open Scope cat_scope.

Set Universe Polymorphism.
(* end hide *)

(* We consider the transport of the symmetric traced monoidal structure of [ktree]s to a subcategory *)

Class Embedding@{uI uJ} (i : Type@{uI}): Type :=
  F: i -> Type@{uJ}.

Class Embedded_initial@{uI uJ} `{Embedding@{uI uJ}} (iI: i) :=
  {
    iI_void: F iI -> void;
    void_iI: void -> F iI
  }.

Class Embedded_sum@{uI uJ} `{Embedding@{uI uJ}} (isum: i -> i -> i) :=
  {
    isum_sum: forall {A B: i}, F (isum A B) -> (F A) + (F B);
    sum_isum: forall {A B: i}, (F A) + (F B) -> F (isum A B)
  }.

(** * Subcategories of [Fun] *)
Section iFun.

Universe uI uJ uY.
(* We consider a subdomain of Type given by a Type [i] and its injection [F] into [Type] *)
Context {i: Type@{uI}}.
Context {iEmbed: Embedding@{uI uJ} i}.
(* We assume that we have an initial element and a bifunctor over i *)
Context {iI: i}.
Context {isum: i -> i -> i}.
Context {FInit: Embedded_initial iI}.
Context {iI_iso: Iso@{uY uJ} Fun iI_void void_iI}.
Context {Fsum: Embedded_sum isum}.
Context {sum_Iso: forall A B, Iso@{uY uJ} Fun (@isum_sum _ _ _ _ A B) sum_isum}.

(* The embedding [F] defines a subcategory of [Fun] *)
Definition iFun (a b: i) := F a -> F b.

Global Instance Eq2_iFun : Eq2 iFun :=
  fun a b => @eq2@{uY _} _ Fun _ (F a) (F b).

Global Instance Id_iFun : Id_ iFun :=
  fun a => @id_@{uY _} _ Fun _ (F a).

(** Function composition *)
Global Instance Cat_iFun : Cat iFun :=
  fun a b c f g => @cat@{uY _} _ Fun _ _ _ _ f g.

(** [void] as an initial object. *)
Global Instance Initial_iI : Initial iFun iI :=
  fun a => cat@{uY _} iI_void empty@{uY uJ}.

(** ** The [sum] coproduct. *)

(** Coproduct elimination *)
Global Instance case_isum : CoprodCase iFun isum :=
  fun {a b c} f g =>  isum_sum >>> @case_@{uY _} _ Fun _ _ _ _ _ f g.

(** Injections *)
Global Instance isum_inl : CoprodInl iFun isum := fun a b => @inl_@{uY _} _ Fun _ _ _ (F b) >>> sum_isum .
Global Instance isum_inr : CoprodInr iFun isum := fun a b => @inr_@{uY _} _ Fun _ _ _ (F a) >>> sum_isum .

End iFun.

(** * Subcategories of [ktree] *)
Section SubK.

Universe uI uE uF uR uT uY.

(* We consider a subdomain of Type given by a Type [i] and its injection [F] into [Type] *)
Context {i: Type@{uI}}.
Context {iEmbed: Embedding@{uI uR} i}.
(* We assume that we have an initial element and a bifunctor over i *)
Context {iI: i}.
Context {isum: i -> i -> i}.
Context {FInit: Embedded_initial iI}.
Context {iI_iso: Iso@{uY uR} Fun iI_void void_iI}.
Context {Fsum: Embedded_sum isum}.
Context {sum_Iso: forall A B, Iso@{uY uR} Fun (@isum_sum _ _ _ _ A B) sum_isum}.

(* The embedding [F] defines a subcategory of [ktree] *)
Definition sktree (E: Type@{uE} -> Type@{uF}) (A B: i) : Type@{uT}
  := F A -> itree@{uE uF uR uT} E (F B).

(** ** Categorical operations *)

Section Operations.

Context {E : Type@{uE} -> Type@{uF}}.

Let sktree := sktree E.

(* Utility function to lift a pure ([iFun]) computation into sktree *)
Definition lift_sktree {A B: i} (f : F A -> F B) : sktree A B := lift_ktree f.
Definition iI_voidl : ktree@{uR uT} E (F iI) void := lift_ktree_ E _ _ iI_void.
Definition void_iIl : ktree@{uR uT} E void (F iI) := lift_ktree_ E _ _ void_iI.

Definition isum_suml {A B : i}
  : ktree@{uR uT} E (F (isum A B)) (sum (F A) (F B))
  := lift_ktree_ E _ _ (@isum_sum _ _ _ _ A B).
Definition sum_isuml {A B : i}
  : ktree@{uR uT} E (sum (F A) (F B)) (F (isum A B))
  := lift_ktree_ E _ _ (@sum_isum _ _ _ _ A B).

(** *** Category *)

Definition eutt_sktree {A B} (d1 d2 : sktree A B) : Prop
  := @eq2@{uY _} _ (ktree E) _ _ _ d1 d2.
Global Instance Eq2_sktree : Eq2 sktree := @eutt_sktree.

(** Composition *)
Global Instance Cat_sktree : Cat sktree :=
  fun (A B C: i) (k: ktree E (F A) (F B)) (k': ktree E (F B) (F C)) =>
    @cat@{uY _} Type@{uR} _ _ _ _ _ k k': ktree E _ _.

(** Identity morphism *)
Global Instance Id_sktree : Id_ sktree :=
  fun A => id_@{uY _} (F A).

(** *** Symmetric monoidal category *)

(** Initial object, monoidal unit *)
Global Instance Initial_iI_sktree : Initial@{uI uT} sktree iI :=
  fun A => cat@{uY _} iI_voidl empty@{uY _}.

(** The tensor product is given by the coproduct *)
Global Instance Case_sktree : @CoprodCase@{uI uT} i sktree isum :=
  fun (a b c: i) (ska: ktree _ _ _) skb => cat@{uY _} isum_suml (case_@{uY _} ska skb).

Global Instance Inl_sktree : CoprodInl sktree isum :=
  fun _ _ => cat@{uY _} inl_@{uY _} sum_isuml.

Global Instance Inr_sktree : CoprodInr sktree isum :=
  fun _ _ => cat@{uY _} inr_@{uY _} sum_isuml.

Global Instance Iter_sktree : Iter sktree isum :=
  fun A B (f : ktree E (F A) (F (isum A B))) =>
    iter@{uY _} (cat@{uY _} f isum_suml) : ktree E (F A) (F B).

End Operations.

End SubK.

Notation iter := (@CategoryOps.iter _ (sktree _) _ _ _ _).

(** Traced monoidal category *)
Notation sloop := (@CategoryOps.loop _ (sktree _) _ _ _ _ _ _ _ _ _ _).
